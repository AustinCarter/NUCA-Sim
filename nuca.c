/* nuca.c - cache module routines */

/* SimpleScalar(TM) Tool Suite
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 * All Rights Reserved. 
 * 
 * THIS IS A LEGAL DOCUMENT, BY USING SIMPLESCALAR,
 * YOU ARE AGREEING TO THESE TERMS AND CONDITIONS.
 * 
 * No portion of this work may be used by any commercial entity, or for any
 * commercial purpose, without the prior, written permission of SimpleScalar,
 * LLC (info@simplescalar.com). Nonprofit and noncommercial use is permitted
 * as described below.
 * 
 * 1. SimpleScalar is provided AS IS, with no warranty of any kind, express
 * or implied. The user of the program accepts full responsibility for the
 * application of the program and the use of any results.
 * 
 * 2. Nonprofit and noncommercial use is encouraged. SimpleScalar may be
 * downloaded, compiled, executed, copied, and modified solely for nonprofit,
 * educational, noncommercial research, and noncommercial scholarship
 * purposes provided that this notice in its entirety accompanies all copies.
 * Copies of the modified software can be delivered to persons who use it
 * solely for nonprofit, educational, noncommercial research, and
 * noncommercial scholarship purposes provided that this notice in its
 * entirety accompanies all copies.
 * 
 * 3. ALL COMMERCIAL USE, AND ALL USE BY FOR PROFIT ENTITIES, IS EXPRESSLY
 * PROHIBITED WITHOUT A LICENSE FROM SIMPLESCALAR, LLC (info@simplescalar.com).
 * 
 * 4. No nonprofit user may place any restrictions on the use of this software,
 * including as modified by the user, by any other authorized user.
 * 
 * 5. Noncommercial and nonprofit users may distribute copies of SimpleScalar
 * in compiled or executable form as set forth in Section 2, provided that
 * either: (A) it is accompanied by the corresponding machine-readable source
 * code, or (B) it is accompanied by a written offer, with no time limit, to
 * give anyone a machine-readable copy of the corresponding source code in
 * return for reimbursement of the cost of distribution. This written offer
 * must permit verbatim duplication by anyone, or (C) it is distributed by
 * someone who received only the executable form, and is accompanied by a
 * copy of the written offer of source code.
 * 
 * 6. SimpleScalar was developed by Todd M. Austin, Ph.D. The tool suite is
 * currently maintained by SimpleScalar LLC (info@simplescalar.com). US Mail:
 * 2395 Timbercrest Court, Ann Arbor, MI 48105.
 * 
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "nuca.h"

/* cache access macros */
#define CACHE_TAG(cp, addr)	((addr) >> (cp)->tag_shift)
#define CACHE_SET(cp, addr)	(((addr) >> (cp)->set_shift) & (cp)->set_mask)
#define CACHE_BLK(cp, addr)	((addr) & (cp)->blk_mask)
#define CACHE_BANK(cp, addr) (((addr) >> (cp)->bank_shift) & (cp)->bank_mask)
#define CACHE_TAGSET(cp, addr)	((addr) & (cp)->tagset_mask)

/* extract/reconstruct a block address */
#define CACHE_BADDR(cp, addr)	((addr) & ~(cp)->blk_mask)
#define CACHE_MK_BADDR(cp, tag, bank, set)					\
  (((tag) << (cp)->tag_shift) | ((bank) << (cp)->bank_shift) | ((set) << (cp)->set_shift))

/* index an array of cache blocks, non-trivial due to variable length blocks */
#define NUCA_CACHE_BINDEX(cp, blks, i)					\
  ((struct nuca_cache_blk_t *)(((char *)(blks)) +				\
			  (i)*(sizeof(struct nuca_cache_blk_t) +		\
			       ((cp)->balloc				\
				? (cp)->bsize*sizeof(byte_t) : 0))))

/* cache data block accessor, type parameterized */
#define __CACHE_ACCESS(type, data, bofs)				\
  (*((type *)(((char *)data) + (bofs))))

/* cache data block accessors, by type */
#define CACHE_DOUBLE(data, bofs)  __CACHE_ACCESS(double, data, bofs)
#define CACHE_FLOAT(data, bofs)	  __CACHE_ACCESS(float, data, bofs)
#define CACHE_WORD(data, bofs)	  __CACHE_ACCESS(unsigned int, data, bofs)
#define CACHE_HALF(data, bofs)	  __CACHE_ACCESS(unsigned short, data, bofs)
#define CACHE_BYTE(data, bofs)	  __CACHE_ACCESS(unsigned char, data, bofs)

/* cache block hashing macros, this macro is used to index into a cache
   set hash table (to find the correct block on N in an N-way cache), the
   cache set index function is CACHE_SET, defined above */
#define CACHE_HASH(cp, key)						\
  (((key >> 24) ^ (key >> 16) ^ (key >> 8) ^ key) & ((cp)->hsize-1))

/* copy data out of a cache block to buffer indicated by argument pointer p */
#define CACHE_BCOPY(cmd, blk, bofs, p, nbytes)	\
  if (cmd == Read)							\
    {									\
      switch (nbytes) {							\
      case 1:								\
	*((byte_t *)p) = CACHE_BYTE(&blk->data[0], bofs); break;	\
      case 2:								\
	*((half_t *)p) = CACHE_HALF(&blk->data[0], bofs); break;	\
      case 4:								\
	*((word_t *)p) = CACHE_WORD(&blk->data[0], bofs); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      *((word_t *)p) = CACHE_WORD(&blk->data[0], bofs);	\
	      p += 4; bofs += 4;					\
	    }\
	}\
      }\
    }\
  else /* cmd == Write */						\
    {									\
      switch (nbytes) {							\
      case 1:								\
	CACHE_BYTE(&blk->data[0], bofs) = *((byte_t *)p); break;	\
      case 2:								\
        CACHE_HALF(&blk->data[0], bofs) = *((half_t *)p); break;	\
      case 4:								\
	CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p); break;	\
      default:								\
	{ /* >= 8, power of two, fits in block */			\
	  int words = nbytes >> 2;					\
	  while (words-- > 0)						\
	    {								\
	      CACHE_WORD(&blk->data[0], bofs) = *((word_t *)p);		\
	      p += 4; bofs += 4;					\
	    }\
	}\
    }\
  }

/* bound sqword_t/dfloat_t to positive int */
#define BOUND_POS(N)		((int)(MIN(MAX(0, (N)), 2147483647)))

/* where to insert a block onto the ordered way chain */
enum list_loc_t { Head, Tail };

/* insert BLK into the order way chain in SET at location WHERE */
// static void
// update_way_list(struct cache_set_t *set,	/* set contained way chain */
// 		struct nuca_cache_blk_t *blk,	/* block to insert */
// 		enum list_loc_t where)		/* insert location */
// {
//   /* unlink entry from the way list */
//   if (!blk->way_prev && !blk->way_next)
//     {
//       /* only one entry in list (direct-mapped), no action */
//       assert(set->way_head == blk && set->way_tail == blk);
//       /* Head/Tail order already */
//       return;
//     }
//   /* else, more than one element in the list */
//   else if (!blk->way_prev)
//     {
//       assert(set->way_head == blk && set->way_tail != blk);
//       if (where == Head)
// 	{
// 	  /* already there */
// 	  return;
// 	}
//       /* else, move to tail */
//       set->way_head = blk->way_next;
//       blk->way_next->way_prev = NULL;
//     }
//   else if (!blk->way_next)
//     {
//       /* end of list (and not front of list) */
//       assert(set->way_head != blk && set->way_tail == blk);
//       if (where == Tail)
// 	{
// 	  /* already there */
// 	  return;
// 	}
//       set->way_tail = blk->way_prev;
//       blk->way_prev->way_next = NULL;
//     }
//   else
//     {
//       /* middle of list (and not front or end of list) */
//       assert(set->way_head != blk && set->way_tail != blk);
//       blk->way_prev->way_next = blk->way_next;
//       blk->way_next->way_prev = blk->way_prev;
//     }

//   /* link BLK back into the list */
//   if (where == Head)
//     {
//       /* link to the head of the way list */
//       blk->way_next = set->way_head;
//       blk->way_prev = NULL;
//       set->way_head->way_prev = blk;
//       set->way_head = blk;
//     }
//   else if (where == Tail)
//     {
//       /* link to the tail of the way list */
//       blk->way_prev = set->way_tail;
//       blk->way_next = NULL;
//       set->way_tail->way_next = blk;
//       set->way_tail = blk;
//     }
//   else
//     panic("bogus WHERE designator");
// }

/* create and initialize a general cache structure */
struct nuca_cache_t *			/* pointer to cache created */
nuca_cache_create(char *name,		/* name of the cache */
	     int nsets,			/* total number of sets in cache */
	     int bsize,			/* block (line) size of cache */
	     int balloc,		/* allocate data space for blocks? */
	     int usize,			/* size of user data to alloc w/blks */
	     int assoc,			/* associativity of cache */
	     enum nuca_cache_policy policy,	/* replacement policy w/in sets */
       enum nuca_search_policy search_policy,	/* replacement policy w/in sets */
       enum nuca_mapping_policy mapping_policy,	/* replacement policy w/in sets */
	     /* block access function, see description w/in struct cache def */
	     unsigned int (*blk_access_fn)(enum mem_cmd cmd,
					   md_addr_t baddr, int bsize,
					   struct nuca_cache_blk_t *blk,
					   tick_t now),
	     unsigned int hit_latency, /* latency in cycles for a hit */
       unsigned int nbanks, /* number of banks */
       unsigned int hit_count /* determines number of hits needed for a generational promotion */) 
{
  struct nuca_cache_t *cp;

  /* check all cache parameters */
  if (nsets <= 0)
    fatal("cache size (in sets) `%d' must be non-zero", nsets);
  if (nbanks <= 0)
      fatal("number of banks `%d' must be non-zero", nbanks);
  if ((nsets & (nsets-1)) != 0)
    fatal("cache size (in sets) `%d' is not a power of two", nsets);
  /* blocks must be at least one datum large, i.e., 8 bytes for SS */
  if (bsize < 8)
    fatal("cache block size (in bytes) `%d' must be 8 or greater", bsize);
  if ((bsize & (bsize-1)) != 0)
    fatal("cache block size (in bytes) `%d' must be a power of two", bsize);
  if (usize < 0)
    fatal("user data size (in bytes) `%d' must be a positive value", usize);
  if (assoc <= 0)
    fatal("cache associativity `%d' must be non-zero and positive", assoc);
  if ((assoc & (assoc-1)) != 0)
    fatal("cache associativity `%d' must be a power of two", assoc);
  if (!blk_access_fn)
    fatal("must specify miss/replacement functions");

  /* allocate the cache structure */
  cp = (struct nuca_cache_t*)
    calloc(1, sizeof(struct nuca_cache_t));
  if (!cp)
    fatal("out of virtual memory");

  /* initialize user parameters */
  cp->name = mystrdup(name);
  cp->nsets = nsets;
  cp->nbanks = nbanks;
  cp->bsize = bsize;
  cp->balloc = balloc;
  cp->usize = usize;
  cp->assoc = assoc;
  cp->policy = policy;
  cp->search_policy = search_policy;
  cp->hit_latency = hit_latency;
  cp->hitCount = hit_count;

  /* miss/replacement functions */
  cp->blk_access_fn = blk_access_fn;
  debug("%s: bsize     = %d", cp->name, bsize);
  debug("%s: nsets     = %d", cp->name, nsets);
  debug("%s: nbanks    = %d", cp->name, nbanks);
  debug("%s: usize    = %d", cp->name, assoc*bsize*nsets);
  debug("%s: usize-log    = %d", cp->name, log_base2(assoc*bsize*nsets));


  /* compute derived parameters */
  cp->blk_mask = bsize-1;
  cp->set_shift = log_base2(bsize);
  cp->bank_shift = cp->set_shift + log_base2(nsets);
  cp->set_mask = nsets-1;
  cp->bank_mask = (nbanks/assoc)-1;
  cp->tag_shift = cp->bank_shift + log_base2(nbanks/assoc);
  cp->tag_mask = (1 << (32 - cp->tag_shift))-1;
  cp->tagset_mask = ~cp->blk_mask;
  cp->bus_free = 0;

  /* print derived parameters during debug */
  debug("%s: cp->blk_mask  = 0x%08x", cp->name, cp->blk_mask);
  debug("%s: cp->set_shift = %d", cp->name, cp->set_shift);
  debug("%s: cp->set_mask  = 0x%08x", cp->name, cp->set_mask);
  debug("%s: cp->bank_shift = %d", cp->name, cp->bank_shift);
  debug("%s: cp->bank_mask  = 0x%08x", cp->name, cp->bank_mask);
  debug("%s: cp->tag_shift = %d", cp->name, cp->tag_shift);
  debug("%s: cp->tag_mask  = 0x%08x", cp->name, cp->tag_mask);

  /* initialize cache stats */
  cp->hits = 0;
  cp->misses = 0;
  cp->replacements = 0;
  cp->writebacks = 0;
  cp->invalidations = 0;
  cp->bank_hits = (counter_t**)calloc(nbanks/assoc, sizeof(counter_t*));
  int bcounter = 0;
  for (bcounter = 0; bcounter<nbanks/assoc; bcounter++){
    cp->bank_hits[bcounter] = (counter_t*)calloc(assoc, sizeof(counter_t));
  }

  /* blow away the last block accessed */
  cp->last_tagset = 0;
  cp->last_blk = NULL;

  int z = 0;
  int b = 0;
  /* allocate banks */ //2d array of banks
  /* [bank set, way]*/
  cp->banks = (struct nuca_cache_bank_t**)calloc(nbanks/assoc, sizeof(struct nuca_cache_bank_t*));
  for (b=0; b<nbanks/assoc; b++){
    cp->banks[b] = (struct nuca_cache_bank_t*)calloc(assoc, sizeof(struct nuca_cache_bank_t));
  }
  

  /* allocate sets */
  int s = 0;
  int w = 0; // way number
  //Note: consecutive banks are part of the associative bank sets
  FILE *bank_org_file;
  char* path = "./bank_orgs/";
  char filepath[64];
  sprintf(filepath, "%sbanks_%s_%d.txt", path, 
          (mapping_policy == SIMPLE ? "simple" : mapping_policy == SHARED ? "shared" 
          : mapping_policy == FAIR ? "fair" : (abort(), "")), 
          log_base2(assoc*bsize*nsets));
  debug ("filepath: %s\n",filepath);
  bank_org_file = fopen(filepath, "r");
  if (bank_org_file == NULL){
    fatal("file does not exist at path: %s", filepath);
  }
  for (b=0; b<nbanks/assoc; b++){
    for (z=0; z<assoc; z++){
      cp->banks[b][z].sets = (struct nuca_cache_set_t*)calloc(nsets, sizeof(struct nuca_cache_set_t));
      fscanf(bank_org_file, "%d", &(cp->banks[b][z].access_time));
      debug("Access Time: %d\n", cp->banks[b][z].access_time);
      cp->banks[b][z].way_number = w; //
      /* allocate data blocks */
      for (s=0; s<nsets; s++){
        cp->banks[b][z].sets[s].blk = (struct nuca_cache_blk_t*)calloc(1, sizeof(struct nuca_cache_blk_t));
        cp->banks[b][z].sets[s].blk->status = 0;
        cp->banks[b][z].sets[s].blk->tag = 0;
        cp->banks[b][z].sets[s].blk->ready = 0;
      }

    }
  }
  fclose(bank_org_file);
  return cp;
}

/* parse policy */
enum nuca_cache_policy			/* replacement policy enum */
nuca_cache_char2policy(char c)		/* replacement policy as a char */
{
  switch (c) {
  case 'z': return ZERO_COPY;
  case 'o': return ONE_COPY;
  default: fatal("bogus replacement policy, `%c'", c);
  }
}

/* parse policy */
enum nuca_search_policy			/* search policy enum */
nuca_search_char2policy(char c)		/* search policy as a char */
{
  switch (c) {
  case 'i': return INCREMENTAL;
  case 'm': return MULTICAST;
  case 'l': return LIMITED_MULTICAST;
  case 'p': return PARTITIONED_MULTICAST;
  default: fatal("bogus search policy, `%c'", c);
  }
}

/* parse policy */
enum nuca_mapping_policy			/* search policy enum */
nuca_mapping_char2policy(char c)		/* search policy as a char */
{
  switch (c) {
  case 's': return SIMPLE;
  case 'h': return SHARED;
  case 'f': return FAIR;
  default: fatal("bogus mapping policy, `%c'", c);
  }
}

/* print cache configuration */
void
nuca_cache_config(struct nuca_cache_t *cp,	/* cache instance */
	     FILE *stream)		/* output stream */
{
  fprintf(stream,
	  "cache: %s: %d sets, %d byte blocks, %d bytes user data/block\n",
	  cp->name, cp->nsets, cp->bsize, cp->usize);
  fprintf(stream,
	  "cache: %s: %d-way, `%s' replacement policy, write-back\n",
	  cp->name, cp->assoc,
	  cp->policy == ZERO_COPY ? "Zero-Copy"
	  : cp->policy == ONE_COPY ? "One-Copy"
	  : (abort(), ""));
}

/* register cache stats */
void
nuca_cache_reg_stats(struct nuca_cache_t *cp,	/* cache instance */
		struct stat_sdb_t *sdb)	/* stats database */
{
  char buf[512], buf1[512], *name;

  /* get a name for this cache */
  if (!cp->name || !cp->name[0])
    name = "<unknown>";
  else
    name = cp->name;

  sprintf(buf, "%s.accesses", name);
  sprintf(buf1, "%s.hits + %s.misses", name, name);
  stat_reg_formula(sdb, buf, "total number of accesses", buf1, "%12.0f");
  sprintf(buf, "%s.hits", name);
  stat_reg_counter(sdb, buf, "total number of hits", &cp->hits, 0, NULL);
  sprintf(buf, "%s.misses", name);
  stat_reg_counter(sdb, buf, "total number of misses", &cp->misses, 0, NULL);
  sprintf(buf, "%s.replacements", name);
  stat_reg_counter(sdb, buf, "total number of replacements",
		 &cp->replacements, 0, NULL);
  sprintf(buf, "%s.writebacks", name);
  stat_reg_counter(sdb, buf, "total number of writebacks",
		 &cp->writebacks, 0, NULL);
  sprintf(buf, "%s.invalidations", name);
  stat_reg_counter(sdb, buf, "total number of invalidations",
		 &cp->invalidations, 0, NULL);
  sprintf(buf, "%s.miss_rate", name);
  sprintf(buf1, "%s.misses / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "miss rate (i.e., misses/ref)", buf1, NULL);
  sprintf(buf, "%s.repl_rate", name);
  sprintf(buf1, "%s.replacements / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "replacement rate (i.e., repls/ref)", buf1, NULL);
  sprintf(buf, "%s.wb_rate", name);
  sprintf(buf1, "%s.writebacks / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "writeback rate (i.e., wrbks/ref)", buf1, NULL);
  sprintf(buf, "%s.inv_rate", name);
  sprintf(buf1, "%s.invalidations / %s.accesses", name, name);
  stat_reg_formula(sdb, buf, "invalidation rate (i.e., invs/ref)", buf1, NULL);
  sprintf(buf, "Banks Hits");
  counter_t t = 0;
  counter_t a = 0;
  for (t = 0; t<cp->nbanks/cp->assoc; t++){ //TODO: What does stat reg counter do??
    for (a = 0; a<cp->assoc; a++){
      stat_reg_counter(sdb, buf, "hits for bank", &cp->bank_hits[t][a], 0, NULL);
    }
  }
}

/* print cache stats */
void
nuca_cache_stats(struct nuca_cache_t *cp,		/* cache instance */
	    FILE *stream)		/* output stream */
{
  double sum = (double)(cp->hits + cp->misses);

  fprintf(stream,
	  "cache: %s: %.0f hits %.0f misses %.0f repls %.0f invalidations\n",
	  cp->name, (double)cp->hits, (double)cp->misses,
	  (double)cp->replacements, (double)cp->invalidations);
  fprintf(stream,
	  "cache: %s: miss rate=%f  repl rate=%f  invalidation rate=%f\n",
	  cp->name,
	  (double)cp->misses/sum, (double)(double)cp->replacements/sum,
	  (double)cp->invalidations/sum);
}

/* access a cache, perform a CMD operation on cache CP at address ADDR,
   places NBYTES of data at *P, returns latency of operation if initiated
   at NOW, places pointer to block user data in *UDATA, *P is untouched if
   cache blocks are not allocated (!CP->BALLOC), UDATA should be NULL if no
   user data is attached to blocks */
unsigned int				/* latency of access in cycles */
nuca_cache_access(struct nuca_cache_t *cp,	/* cache to access */
	     enum mem_cmd cmd,		/* access type, Read or Write */
	     md_addr_t addr,		/* address of access */
	     void *vp,			/* ptr to buffer for input/output */
	     int nbytes,		/* number of bytes to access */
	     tick_t now,		/* time of access */
	     byte_t **udata,		/* for return of user data ptr */
	     md_addr_t *repl_addr)	/* for address of replaced block */
{
  byte_t *p = vp;
  md_addr_t bank = CACHE_BANK(cp, addr);
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  md_addr_t bofs = CACHE_BLK(cp, addr);
  struct nuca_cache_blk_t *blk, *repl;
  int lat = 0;

  /* check alignments */
  if ((nbytes & (nbytes-1)) != 0 || (addr & (nbytes-1)) != 0){
    fatal("cache: access error: bad size or alignment, addr 0x%08x", addr);
  }

  /* access must fit in cache block */
  if ((addr + nbytes) > ((addr & ~cp->blk_mask) + cp->bsize)){
    fatal("cache: access error: access spans block, addr 0x%08x", addr);
  }
    /* permissions are checked on cache misses */
    /* TODO: linear search the way list, need to go bank by bank */
  int acc_time = 0;
  int w = 0;
  int invalidWay = -1;
  for (w = 0; w < cp->assoc; w++){
    blk=cp->banks[bank][w].sets[set].blk;
    debug("bank: %d, way: %d, set: %d, addr: %x, cache tag: %x, block tag: %x", bank, w, set, addr, blk->tag, tag);
    acc_time += cp->banks[bank][w].access_time;
    if (!(blk->status & CACHE_BLK_VALID)){
      invalidWay = w;
    }
    if (blk->tag == tag && (blk->status & CACHE_BLK_VALID)){
      cp->bank_hits[bank][w]++;
      return cache_hit(cp, cp->banks[bank], w, set, blk, cmd, nbytes, p, bofs, addr, now, acc_time);
    }
  }
  /* cache block not found */

  /* **MISS** */
  cp->misses++;

  /* select the appropriate block to replace, and re-link this entry to
     the appropriate place in the way list */

  if (invalidWay == -1){
    repl = cp->banks[bank][cp->assoc-1].sets[set].blk;

    switch (cp->policy) {
    case ZERO_COPY:
      repl = cp->banks[bank][cp->assoc-1].sets[set].blk;
      break;
    case ONE_COPY:
      repl = cp->banks[bank][cp->assoc-1].sets[set].blk; //save evicted one temporarily
      for (w = cp->assoc-1; w > 0; w--){
        cp->banks[bank][w].sets[set].blk = cp->banks[bank][w-1].sets[set].blk; //move all blocks one bank back, evicting last block
      }
      cp->banks[bank][0].sets[set].blk = repl; //this way block still different, just need to reset stuff
      break;
    default:
      panic("bogus replacement policy");
    }
  }
  else{
    repl = cp->banks[bank][invalidWay].sets[set].blk;
  }
  /* write back replaced block data */
  if (repl->status & CACHE_BLK_VALID)
    {
      cp->replacements++;

      /* don't replace the block until outstanding misses are satisfied */
      lat += BOUND_POS(repl->ready - now);
 
      /* stall until the bus to next level of memory is available */
      lat += BOUND_POS(cp->bus_free - (now + lat));
 
      /* track bus resource usage */
      cp->bus_free = MAX(cp->bus_free, (now + lat)) + 1;

      if (repl->status & CACHE_BLK_DIRTY)
      {
        /* write back the cache block */
        cp->writebacks++;
        lat += cp->blk_access_fn(Write,
              CACHE_MK_BADDR(cp, repl->tag, bank, set),
              cp->bsize, repl, now+lat);
      }
    }

  /* update block tags */
  repl->tag = tag;
  repl->status = CACHE_BLK_VALID;	/* dirty bit set on update */
  repl->hitCount = 0;

  /* read data block */
  lat += cp->blk_access_fn(Read, CACHE_BADDR(cp, addr), cp->bsize,
			   repl, now+lat);

  /* update dirty status */
  if (cmd == Write)
    repl->status |= CACHE_BLK_DIRTY;

  /* get user block data, if requested and it exists */
  // if (udata)
  //   *udata = repl->user_data;

  /* update block status */
  repl->ready = now+lat;

  /* return latency of the operation */
  return lat;

}

/* return non-zero if block containing address ADDR is contained in cache
   CP, this interface is used primarily for debugging and asserting cache
   invariants */
int					/* non-zero if access would hit */
nuca_cache_probe(struct nuca_cache_t *cp,		/* cache instance to probe */
	    md_addr_t addr)		/* address of block to probe */
{
  md_addr_t tag = CACHE_TAG(cp, addr);
  md_addr_t set = CACHE_SET(cp, addr);
  md_addr_t bank = CACHE_BANK(cp, addr);
  struct nuca_cache_blk_t *blk;

  /* low-associativity cache, linear search the way list */
  int w = 0;
  for (w = 0; w < cp->assoc; w++){
    blk=cp->banks[bank][w].sets[set].blk;
    if (blk->tag == tag && (blk->status & CACHE_BLK_VALID)){
      return TRUE;
    }
  }
  
  // /* cache block not found */
  return FALSE;
}

int cache_hit(struct nuca_cache_t *cp, struct nuca_cache_bank_t *banks, int wayNumber, md_addr_t set,
              struct nuca_cache_blk_t *blk, enum mem_cmd cmd, int nbytes, byte_t *p, 
              md_addr_t bofs, md_addr_t addr, tick_t now, int acc_time){
    /* **HIT** */
    cp->hits++;
    blk->hitCount++;

    /* copy data out of cache block, if block exists */
    // if (cp->balloc)
    //   {
    //     CACHE_BCOPY(cmd, blk, bofs, p, nbytes);
    //   }

    /* update dirty status */
    if (cmd == Write)
      blk->status |= CACHE_BLK_DIRTY;

    //don't need because only one way per set in bank
    // /* if LRU replacement and this is not the first element of list, reorder */
    // if (blk->way_prev && cp->policy == LRU)
    //   {
    //     /* move this block to head of the way (MRU) list */
    //     update_way_list(&cp->sets[set], blk, Head);
    //   }

    /* tag is unchanged, so hash links (if they exist) are still valid */

    // /* record the last block to hit */
    // cp->last_tagset = CACHE_TAGSET(cp, addr);
    // cp->last_blk = blk;

    // /* get user block data, if requested and it exists */
    // if (udata)
    //   *udata = blk->user_data;

    /* for generational promotion*/
    if (blk->hitCount == cp->hitCount && wayNumber != 0){
      struct nuca_cache_blk_t *temp;
      switch (cp->policy) {
        case ZERO_COPY:
          blk->hitCount = 0;
          banks[wayNumber-1].sets[set].blk->tag = blk->tag;
          banks[wayNumber-1].sets[set].blk->status = CACHE_BLK_VALID;
          banks[wayNumber-1].sets[set].blk->hitCount = 0;
          blk->status = 0;         
          break;
        case ONE_COPY:
          temp = banks[wayNumber-1].sets[set].blk; //save evicted one temporarily
          banks[wayNumber-1].sets[set].blk = banks[wayNumber].sets[set].blk;
          banks[wayNumber].sets[set].blk = temp; //do we keep hit count the same? I think so
          break;
        default:
          panic("bogus replacement policy");
        }

    }

    /* return first cycle data is available to access */
  
    int access_time = acc_time; //default is incremental
      switch (cp->search_policy) {
        case INCREMENTAL:
          break;
        case MULTICAST:
          access_time = banks[wayNumber].access_time;
          break;
        case LIMITED_MULTICAST:
          if (wayNumber > 1){ //TODO 1 is arbitrary, could be any n < assoc
            int w = 0;
            access_time = banks[wayNumber].access_time;
            for (w = 0; w <= 1; w++){
              access_time += banks[w].access_time;
            }
          }
          break;
        case PARTITIONED_MULTICAST:
          access_time = banks[wayNumber].access_time;
          break;
      default:
        panic("bogus search policy");
  }
    debug("Access Time: %d", (int) MAX(access_time, (blk->ready - now)));
    return (int) MAX(access_time, (blk->ready - now));
}
#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"         // Alphabetically after 'checker'.

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an offline backward DRUP proof checker enabled by
// 'opts.checkproofbackward' (requires 'opts.check' also to be enabled).

/*------------------------------------------------------------------------*/

struct BCheckerClause {
  BCheckerClause* next;
  Clause * counterpart;
  uint64_t hash;
  unsigned size;
  bool core;
  bool garbage;
  int literals[1];
};

class BChecker : public Observer {

  Internal * internal;

  // stack of clausal proof
  //
  vector<BCheckerClause*> proof;

  bool inconsistent;            // found or added empty clause

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t num_garbage;         // number of garbage clauses
  uint64_t size_clauses;        // size of clause hash table
  BCheckerClause ** clauses;    // hash table of clauses
  /// NOTE: Can add garbage hash table.

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];                // random numbers for hashing
  uint64_t compute_hash (const vector<int> &);      // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  // enlarge hash table for clauses
  //
  void enlarge_clauses ();

  BCheckerClause * new_clause (const vector<int> & simplified, const uint64_t hash);
  void delete_clause (BCheckerClause *);

  BCheckerClause ** find (const vector<int> &);       // find clause position in hash table
  BCheckerClause * insert (const vector<int> & c);    // insert clause in hash table

  // get the BCheckerClause instance. (intance is allocated if it doesn't exist).
  // 
  BCheckerClause * get_bchecker_clause (Clause *);
  BCheckerClause * get_bchecker_clause (vector<int> &);

  // popping all trail literals up to and including the literal whose antecedent is 'c'.
  //
  void undo_trail_core (Clause * c, int & trail_sz);
  bool is_on_trail (Clause *);
  bool validate_lemma (Clause *);

  struct {

    int64_t added;              // number of added clauses
    int64_t original;           // number of added original clauses
    int64_t derived;            // number of added derived clauses

    int64_t deleted;            // number of deleted clauses

    int64_t assumptions;        // number of assumed literals
    int64_t propagations;       // number of propagated literals

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

    int64_t checks;             // number of implication checks

    int64_t collections;        // garbage collections
    int64_t units;

  } stats;


public:

  BChecker (Internal *);
  ~BChecker ();

  void add_derived_clause (const vector<int> &);
  void delete_clause (const vector<int> &);

  bool validate ();             // validate the clausal proof

  void print_stats ();

  void dump ();                 // for debugging purposes only
};

}

#endif

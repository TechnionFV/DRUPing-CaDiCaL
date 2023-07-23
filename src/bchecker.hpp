#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"
#include "unordered_map"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This observer implements an offline backward DRUP proof checking enabled by
// 'opts.checkproofbackward' (requires 'opts.check' also to be enabled).

/*------------------------------------------------------------------------*/

struct BCheckerClause {
  BCheckerClause* next;
  uint64_t hash;
  unsigned size;
  bool garbage;
  int literals[1];
};

class BChecker {

  Internal * internal;

  // stack of clausal proof
  //
  vector<pair<BCheckerClause*, bool>> proof;

  // stack of clausal proof counterparts accordingly
  //
  vector<Clause*> counterparts;

  // for each counterpart 'c', 'ordering[c]' contains all matching stack indexes
  //
  unordered_map<Clause *, vector<int>> ordering;

  BCheckerClause * get_bchecker_clause (Clause * c);
  BCheckerClause * get_bchecker_clause (int lit);

  void invalidate_counterpart (Clause * c);
  void append_lemma (BCheckerClause* bc, Clause * c);

  bool inconsistent;            // found or added empty clause

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t size_clauses;        // size of clause hash table
  BCheckerClause ** clauses;    // hash table of clauses

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];                      // random numbers for hashing
  uint64_t compute_hash (const vector<int> &);      // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  // enlarge hash table for clauses
  //
  void enlarge_clauses ();

  BCheckerClause * new_clause (const vector<int> & simplified, const uint64_t hash);
  void delete_clause (BCheckerClause *);

  BCheckerClause ** find (Clause *);         // find clause position in hash table
  BCheckerClause * insert (Clause * c);      // insert clause in hash table

  BCheckerClause ** find (const vector<int> &);         // find clause position in hash table
  BCheckerClause * insert (const vector<int> &);      // insert clause in hash table

  // If true, include core unit clauses.
  //
  bool core_units;

  void revive_internal_clause (BCheckerClause *);
  void stagnate_internal_clause (const int i);
  void reactivate_fixed (int );

  // popping all trail literals up to and including the literal whose antecedent is 'c'.
  //
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  void undo_trail_literal (int );
  bool is_on_trail (Clause *);

  void conflict_analysis_core ();

  void mark_core (Clause *);
  void mark_core_trail_antecedents ();
  void put_units_back ();

  bool shrink_internal_trail (const int);
  void clear ();
  bool validate_lemma (Clause *);

  void check_data ();

  bool validating;      // On during validating

  struct {

    int64_t added;              // number of added clauses
    int64_t original;           // number of added original clauses
    int64_t derived;            // number of added derived clauses
    int64_t counterparts;       // number of added counterpart references

    int64_t deleted;            // number of deleted clauses

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

  } stats;

public:

  BChecker (Internal *, bool core_units = 0);
  ~BChecker ();

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int);
  void add_derived_empty_clause ();
  void delete_clause (Clause *);

  void update_moved_counterparts ();

  bool validate ();             // validate the clausal proof

  void print_stats ();

  void dump ();                 // for debugging purposes only
};

}

#endif

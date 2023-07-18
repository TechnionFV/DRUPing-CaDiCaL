#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This observer implements an offline backward DRUP proof checking enabled by
// 'opts.checkproofbackward' (requires 'opts.check' also to be enabled).

/*------------------------------------------------------------------------*/

struct BCheckerClause {
  BCheckerClause* next;
  Clause * counterpart;
  uint64_t hash;
  unsigned size;
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

  BCheckerClause ** find (const vector<int> &);         // find clause position in hash table
  BCheckerClause * insert (const vector<int> & c);      // insert clause in hash table

  // If true, include core unit clauses.
  //
  bool core_units;

  // get the BCheckerClause instance. (intance is allocated if it doesn't exist).
  // 
  BCheckerClause * get_bchecker_clause (Clause *);
  BCheckerClause * get_bchecker_clause (vector<int> &);

  void revive_internal_clause (BCheckerClause *);
  void stagnate_internal_clause (BCheckerClause *);
  void reactivate_fixed (int );
  void put_trail_literal_in_place (Clause *);

  void undo_trail_literal (int );
  // popping all trail literals up to and including the literal whose antecedent is 'c'.
  //
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  bool shrink_internal_trail (const int);
  bool is_on_trail (Clause *);
  void mark_core_trail_antecedents ();

  void mark_core (Clause *);

  void conflict_analysis_core (const int decisions);
  bool validate_lemma (Clause *);
  void check_counterparts ();

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

  BChecker (Internal *, bool core_units = false);
  ~BChecker ();

  void add_derived_clause (const vector<int> &);
  void delete_clause (const vector<int> &);

  ///CONSULT:|NOTE: In most of the palces were the proof is notified with a new learned clause,
  //                the Clause reference can easily be obtained. However, there are two
  //                cases were this does not hold:
  //                1) When performing a round of Tarjan's algorithm (equivalent literal substitution)
  //                   in decompose.cpp.. Need to consult..
  //                2) While conflicting assumptions clause isn't actually allocated in the internal solver,
  //                   the proof would still be notified with it so its correctness can be checked.
  //                   In this case, we can simply create a new Clause object for the conflicting assumptions.
  ///TODO:|NOTE: Caching counterparts is so fragile as it needs to be called right after
  //             proof->add_derived_clause... Need to find a better solution.
  void cache_counterpart (Clause *);
  void update_moved_counterparts ();
  bool invalidated_counterpart (Clause *);

  bool validate ();             // validate the clausal proof

  void print_stats ();

  void dump ();                 // for debugging purposes only
};

}

#endif

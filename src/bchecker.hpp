#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"         // Alphabetically after 'checker'.

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an offline backward DRUP proof checker enabled by
// 'opts.checkproofbackward' (requires 'opts.check' also to be enabled).

/*------------------------------------------------------------------------*/

class BChecker : public Observer {

  Internal * internal;

  vector<vector<int>> proof;    // clausal proof

  bool inconsistent;            // found or added empty clause

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

  // The following three implement the 'Observer' interface.
  //
  void add_original_clause (const vector<int> &);
  void add_derived_clause (const vector<int> &);
  void delete_clause (const vector<int> &);

  bool validate ();             // validate the clausal proof

  void print_stats ();
};

}

#endif

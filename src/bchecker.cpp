#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

BChecker::BChecker (Internal * i) : internal (i)
{
  LOG ("BCHECKER new");
  memset (&stats, 0, sizeof (stats));           // Initialize statistics.
}

BChecker::~BChecker () {
  LOG ("BCHECKER delete");
}

/*------------------------------------------------------------------------*/

void BChecker::add_original_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER addition of original clause");
  stats.added++;
  stats.original++;
  STOP (bchecking);
}

void BChecker::add_derived_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER addition of derived clause");
  stats.added++;
  stats.derived++;
  STOP (bchecking);
}

/*------------------------------------------------------------------------*/

void BChecker::delete_clause (const vector<int> & c) {
  if (inconsistent) return;
  START (bchecking);
  LOG (c, "BCHECKER bchecking deletion of clause");
  stats.deleted++;
  STOP (bchecking);
}

}

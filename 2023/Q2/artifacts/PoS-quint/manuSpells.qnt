// -*- mode: Bluespec; -*-
/**
 * This module collects definitions that are ubiquitous.
 * One day they will become the standard library of Quint.
 */
module manuSpells {

  import basicSpells.* from "./basicSpells"

  /// Remove a map entry.
  ///
  /// - @param __map a map to remove an entry from
  /// - @param __key the key of an entry to remove
  /// - @returns a new map that contains all entries of __map
  ///          that do not have the key __key
  pure def safeSet(__map: a -> b, __key: a, __value: b): a -> b = {
    if (__map.has(__key)) {
      __map.set(__key, __value)
    } else {
      __map.keys().union(Set(__key)).mapBy(__k => if (__k == __key) __value else __map.get(__k))
    }
  }

  run safeSetTest = all {
    assert(Map(2 -> 3, 4 -> 5).safeSet(1, 7) == Map(1 -> 7, 2 -> 3, 4 -> 5)),
    assert(Map(2 -> 3, 4 -> 5).safeSet(2, 7) == Map(2 -> 7, 4 -> 5))
  }
}
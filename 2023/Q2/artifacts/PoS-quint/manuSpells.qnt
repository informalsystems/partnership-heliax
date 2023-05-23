// -*- mode: Bluespec; -*-
/**
 * This module collects definitions that are ubiquitous.
 * One day they will become the standard library of Quint.
 */
module manuSpells {

  import basicSpells.* from "./basicSpells"

  /// Safely set a map entry.
  ///
  /// - @param __map a map to set an entry to
  /// - @param __key the key of an entry to set
  /// - @returns a new map that contains all entries of __map
  ///          and an entry for the key __key
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

  /// Compute the minimum of two integers.
  ///
  /// - @param __i first integer
  /// - @param __j second integer
  /// - @returns the minimum of __i and __j
  pure def min(__i: int, __j: int): int = {
    if (__i > __j) __j else __i
  }

  run minTest = all {
    assert(min(3, 4) == 3),
    assert(min(6, 3) == 3),
    assert(min(10, 10) == 10),
    assert(min(-3, -5) == -5),
    assert(min(-5, -3) == -5),
  }

  /// Add a set element.
  /// - @param __set a set to add an element to
  /// - @param __elem an element to add
  /// - @returns a new set that contains all elements of __set and __elem
  pure def setAdd(__set: Set[a], __elem: a): Set[a] = {
    __set.union(Set(__elem))
  }

  run setAddTest = all {
    assert(Set(2, 3, 4, 5) == Set(2, 3, 4).setAdd(5)),
    assert(Set(3) == Set(3).setAdd(3)),
  }
}
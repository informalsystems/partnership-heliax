// -*- mode: Bluespec; -*-
/**
 *
 * Manuel Bravo, Informal Systems, 2023
 */
module helperFunctions {

  import basicSpells.* from "./basicSpells"
  import extraSpells.* from "./extraSpells"
  import Dec.* from "./dec"
  import types.* from "./namada-types"

    pure def slashProcessingDelay = CUBIC_OFFSET + UNBONDING_OFFSET

    pure def inRedelegationSlashingWindow(infractionEpoch: Epoch, redelegationStart: Epoch, redelegationEnd: Epoch): bool = {
      redelegationStart - UNBONDING_OFFSET - CUBIC_OFFSET <= infractionEpoch and infractionEpoch < redelegationEnd
    }

    pure def endRedelegationFromStart(redelegationStart: Epoch): Epoch = {
      redelegationStart + PIPELINE_OFFSET
    }

    pure def startRedelegationFromEnd(redelegationEnd: Epoch): Epoch = {
      redelegationEnd - PIPELINE_OFFSET
    }

    // **************************************************************************
    // Delegate helper functions
    // ************************************************************************* 

    // The function addBond adds a bond to a map of bonds. If there is an existing bond with the same 
    // starting epoch, then the function simply adds the amount of tokens to the existing entry.
    // - @param bonds a map of bonds.
    // - @param start the starting epoch of the bond to add.
    // - @param amount the amount of tokens of the bond to add.
    // - @returns a map of bonds accounting for the new bond.
    pure def addBond(bonds: Epoch -> int, start: Epoch, amount: int): Epoch -> int = {
      if (bonds.has(start)) bonds.set(start, bonds.get(start) + amount)
      else bonds.mapSafeSet(start, amount)
    }

    run addBondTest = all {
      val bonds = Map(1 -> 5, 2 -> 3, 6 -> 8)
      all {
        assert(addBond(bonds, 2, 6) == Map(1 -> 5, 2 -> 9, 6 -> 8)),
        assert(addBond(bonds, 3, 6) == Map(1 -> 5, 2 -> 3, 3 -> 6, 6 -> 8)),
      }
    }

    // **************************************************************************
    // Unbond helper functions
    // ************************************************************************* 

    // The function unbonds a bond record contraint to a maximum amount (acc.remainder).
    // - @param acc a record with three fields:
    //   - remainder: the maximum amount of tokens to be unbonded.
    //   - toRemove: a set of bond records which includes the set of bond records that have been unbonded so far.
    //   - new: a bond record with start epoch equal to -1.
    // - @param bond the bond record to be unbonded by the function.
    // - @returns an update acc record: subtracts the minimum between bond.amount and acc.remainder from acc.remainder; adds the bond to acc.toRemove;
    // and if bond.amount if gretaer than acc.remainder (meaning that the bond is only partially unbonded), creates a new bond record in acc.new
    // of bond.amount - acc.remainder tokens.
    pure def unbondBond(acc: {remainder: int, toRemove: Set[Epoch], new: {start: int, amount: int}}, bond: {start: int, amount: int}): {remainder: int, toRemove: Set[Epoch], new: {start: int, amount: int}} = { 
      val amountUnbonded = min(bond.amount, acc.remainder)
      {remainder: acc.remainder - amountUnbonded,
       toRemove: if (bond.amount <= acc.remainder) acc.toRemove.setAdd(bond.start) else acc.toRemove,
       new: if (bond.amount > acc.remainder) {start: bond.start, amount: bond.amount - acc.remainder} else acc.new}
    }

    run unbondBondTest = all {
      assert(unbondBond({remainder: 10, toRemove: Set(9, 8), new: {start: -1, amount: 0}}, {start: 6, amount: 5}) ==
             {remainder: 5, toRemove: Set(9, 8, 6), new: {start: -1, amount: 0}}),
      assert(unbondBond({remainder: 10, toRemove: Set(9, 8), new: {start: -1, amount: 0}}, {start: 6, amount: 11}) ==
             {remainder: 0, toRemove: Set(9, 8), new: {start: 6, amount: 1}})
    }

    // The function `iterateBondsUpToAmount` computes the set of bonds that have to be unbonded in order to unbond a given amount. To do so, it iterates
    // over a map of bonds in decreasing starting epoch order until the amount is reached. For each iterated bond, the function calls unbondBond while
    // there are still tokens to be unbonded.
    // - @param bonds a map of bonds that can be unbonded.
    // - @param amount the amount of tokens that have to be unbonded.
    // - @returns a record with two fields: toRemove the set of bonds starting epochs that have been unbonded and a new bond 
    //   that contains a bond record (starting epoch and amount) if a bond has to be partially unbonded or a bond record with start epoch equal to -1
    //   otherwise, indicating that no bond has to be partially unbonded.
    pure def iterateBondsUpToAmount(bonds: Epoch -> int,  amount: int): {toRemove: Set[Epoch], new: {start: int, amount: int}} = {
      val setEpochs = sortSetDecreasing(bonds.keys())
      val result = setEpochs.foldl({remainder: amount, toRemove: Set(), new: {start: -1, amount: 0}},
                                   (acc, e) => if (acc.remainder == 0) acc else unbondBond(acc, {start: e, amount: bonds.get(e)}))
      {toRemove: result.toRemove, new: result.new}
    }

    run iterateBondsUpToAmountTest = {
      val bonds = Map(1 -> 5, 2 -> 3, 6 -> 8)
      all {
        assert(iterateBondsUpToAmount(bonds, 8) == {toRemove: Set(6), new: {start: -1, amount: 0}}),
        assert(iterateBondsUpToAmount(bonds, 10) == {toRemove: Set(6), new: {start: 2, amount: 1}}),
        assert(iterateBondsUpToAmount(bonds, 11) == {toRemove: Set(6, 2), new: {start: -1, amount: 0}}),
        assert(iterateBondsUpToAmount(bonds, 12) == {toRemove: Set(6, 2), new: {start: 1, amount: 4}})
      }
    }

    // **************************************************************************
    // Redelegation helper functions
    // ************************************************************************* 

    // It partially unbonds a redelegated bonds map.
    // - @param redelegatedBonds a map of redelegated bonds from source validator to bond starting epoch at the source validator to amount.
    // - @param epoch the epoch at which the redelegated bonds being modified were bonded to the validator
    // - @param amount the amount of tokens that have to be unbonded.
    // - @returns a ModifiedRedelegation record with all information related to the partially unbonded redelegated tokens. The iteration over source validators is non-deterministic at the moment
    //   (this should be made deterministic). Within a source validator, the iteration over bond starting epochs is done deterministically in the epoch order
    //   picked by the iterateBondsUpToAmount function. At the moment, the iterateBondsUpToAmount function iterates over these epochs in decreasing order.
    //   Note that valsToRemove includes valToModify if different to "" and epochsToRemove includes epochToModify if different to -1.
    pure def computeModifiedRedelegation(redelegatedBonds: RedelegatedBondsMap, epoch: Epoch, amount: int): ModifiedRedelegation = {
      val totalRedelegated = redelegatedBonds.keys().fold(0, (sum, src) => redelegatedBonds.get(src).keys().fold(sum, (acc, e) => acc + redelegatedBonds.get(src).get(e)))
      // If the total amount of redelegated bonds is less than the target amount, then all redelegated bonds must be unbonded.
      if (totalRedelegated <= amount) {epoch: -1, valsToRemove: Set(), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      // If the total amount of redelegated bonds is greater than the target amount, then we need to iterate over the redelegated bonds
      // until the target amount is unbonded. The iteration works as follows (comments interleaved with the folds):
      // 1. It first iterates over source validators. We should iterate in a deterministic order over validators here. Do not know how to do it in Quint at the moment.
      else redelegatedBonds.keys().fold({remainder: amount, modified: {epoch: epoch, valsToRemove: Set(), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}}, 
                                        (acc, src) => if (acc.remainder == 0) acc
                                                      else {
                                                        val totalSrcValidator = redelegatedBonds.get(src).keys().fold(0, (sum, e) => sum + redelegatedBonds.get(src).get(e))
                                                        // 2. For a given validator, if the remaining is greater or equal to the total amount of redelegated tokens of that source validator, the
                                                        //   function removes the source validator: all its redelegated tokens will be  effectively unbonded.
                                                        if (totalRedelegated <= acc.remainder) {remainder: acc.remainder - totalSrcValidator,
                                                                                                modified: acc.modified.with("valsToRemove", acc.modified.valsToRemove.setAdd(src))}
                                                        else {
                                                          // 3. If the remaining is less than the total amount of redelegated tokens of that source validator, the function iterates over all the bonds
                                                          //   of that validator in epoch decreasing order until the remaining is unbonded.
                                                          val resultIteration = iterateBondsUpToAmount(redelegatedBonds.get(src), acc.remainder)
                                                          {remainder: 0,
                                                          modified: if (resultIteration.new.start == -1) acc.modified.with("valsToRemove", acc.modified.valsToRemove.setAdd(src))
                                                                                                                     .with("valToModify", src)
                                                                                                                     .with("epochsToRemove", resultIteration.toRemove)
                                                                    else acc.modified.with("valsToRemove", acc.modified.valsToRemove.setAdd(src))
                                                                                     .with("valToModify", src)
                                                                                     .with("epochsToRemove", resultIteration.toRemove.setAdd(resultIteration.new.start))
                                                                                     .with("epochToModify", resultIteration.new.start)
                                                                                     .with("newAmount", resultIteration.new.amount)}
                                                        }
                                                      }).modified
    }

    // TODO: more tests here when we can iterate over srouce validators deterministically
    run computeModifiedRedelegationTest = {
      val redelegatedBonds = Map("alice" -> Map(2 -> 6, 4 -> 7), "bob" -> Map(1 -> 5, 4 -> 7))
      all {
        assert(computeModifiedRedelegation(redelegatedBonds, 5, 25) == {epoch: -1,
                                                                        valsToRemove: Set(),
                                                                        valToModify: "",
                                                                        epochsToRemove: Set(),
                                                                        epochToModify: -1,
                                                                        newAmount: -1}),
        assert(computeModifiedRedelegation(redelegatedBonds, 5, 30) == {epoch: -1,
                                                                        valsToRemove: Set(),
                                                                        valToModify: "",
                                                                        epochsToRemove: Set(),
                                                                        epochToModify: -1,
                                                                        newAmount: -1})
      }
    }

    // The function computeNewRedelegatedUnbonds computes a set of redelegated unbonds from a set of redelegated bonds.
    // - @param redelegatedBonds a map of redelegated bonds from epoch to RedelegatedBondsMap.
    // - @param unbondedEpochs a set of epochs that indicate the set of epochs unbonded.
    // - @param modified a ModifiedRedelegation record that represents a redelegated bond that it is only partially unbonded.
    // - @returns a map with the redelegated unbonds.
    // The function assumes that
    // - modified.epoch is not in the unbondedEpochs set.
    // - modified.valToModify is in modified.valsToRemove.
    // - modified.epochToModify is in in modified.epochsToRemove.
    pure def computeNewRedelegatedUnbonds(redelegatedBonds: Epoch -> RedelegatedBondsMap, unbondedEpochs: Set[Epoch], modified: ModifiedRedelegation): Epoch -> RedelegatedBondsMap = {
      // Add the modified epoch if there exists and filter out those epochs that do not include redelegations
      val updatedUnbondedEpochs = if (modified.epoch == -1) unbondedEpochs.filter(e => redelegatedBonds.has(e)) else unbondedEpochs.setAdd(modified.epoch).filter(e => redelegatedBonds.has(e))
      updatedUnbondedEpochs.mapBy(start => if (start != modified.epoch) redelegatedBonds.get(start)
                                           else modified.valsToRemove.mapBy(src => if (src != modified.valToModify) redelegatedBonds.get(start).get(src)
                                                                                   else modified.epochsToRemove.mapBy(bondStart => if (bondStart != modified.epochToModify) redelegatedBonds.get(start).get(src).get(bondStart)
                                                                                                                                   else redelegatedBonds.get(start).get(src).get(bondStart) - modified.newAmount)))
    }

    run computeNewRedelegatedUnbondsTest = {
      val redelegatedBonds = Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)),
                                 7 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)))
      val emptyModified = {epoch: -1, valsToRemove: Set(), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedAll = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedValidator = {epoch: 7, valsToRemove: Set("alice"), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedValidatorPartial = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "bob", epochsToRemove: Set(1), epochToModify: -1, newAmount: -1}
      val modifiedEpochPartial = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "bob", epochsToRemove: Set(1, 4), epochToModify: 4, newAmount: 1}                           
      all {
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(), emptyModified) == Map()),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5), emptyModified) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), emptyModified) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), emptyModified) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), modifiedAll) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)),
                                                                                             7 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), modifiedValidator) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)),
                                                                                                   7 -> Map("alice" -> Map(2 -> 1, 4 -> 1)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), modifiedValidatorPartial) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)),
                                                                                                          7 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1)))),
        assert(computeNewRedelegatedUnbonds(redelegatedBonds, Set(5, 6), modifiedEpochPartial) == Map(5 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2)),
                                                                                                      7 -> Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 1)))),                                                                                          
      }
    }

    // The function mergeBondsMap merges two maps of bonds from epoch to bond amount.
    // - @param map1 a map from epoch to int.
    // - @param map2 a map from epoch to int.
    // - @returns a map resulting from merging map1 and map2. If both maps have the same entry, the
    // resulting entry would be the sum of both.
    pure def mergeBondsMap(map1: Epoch -> int, map2: Epoch -> int): Epoch -> int = {
      map1.keys().union(map2.keys()).mapBy(e => if (map1.has(e) and map2.has(e)) map1.get(e) + map2.get(e)
                                                else if (map1.has(e)) map1.get(e) else map2.get(e))

    }

    run mergeBondsMapTest() = all {
      assert(mergeBondsMap(Map(), Map()) == Map()),
      assert(mergeBondsMap(Map(1 -> 2, 2 -> 3), Map()) == Map(1 -> 2, 2 -> 3)),
      assert(mergeBondsMap(Map(), Map(1 -> 2, 2 -> 3)) == Map(1 -> 2, 2 -> 3)),
      assert(mergeBondsMap(Map(1 -> 2, 2 -> 3), Map(3 -> 4, 4 -> 5)) == Map(1 -> 2, 2 -> 3, 3 -> 4, 4 -> 5)),
      assert(mergeBondsMap(Map(1 -> 2, 2 -> 3), Map(2 -> 4, 4 -> 5)) == Map(1 -> 2, 2 -> 7, 4 -> 5)),
    }

    // The function mergeRedelegatedBondsMap merges two RedelegatedBondsMap.
    // - @param map1 a RedelegatedBondsMap.
    // - @param map2 a RedelegatedBondsMap.
    // - @returns a RedelegatedBondsMap resulting from merging map1 and map2. If a given entry is in both maps, the
    // resulting map merges boths leveraging mergeBondsMap
    pure def mergeRedelegatedBondsMap(map1: RedelegatedBondsMap, map2: RedelegatedBondsMap): RedelegatedBondsMap = {
      map1.keys().union(map2.keys()).mapBy(src => if (map1.has(src) and map2.has(src)) mergeBondsMap( map1.get(src), map2.get(src))
                                                  else if (map1.has(src)) map1.get(src) else map2.get(src))

    }

    run mergeRedelegatedBondsMapTest = all {
      assert(mergeRedelegatedBondsMap(Map(), Map()) == Map()),
      assert(mergeRedelegatedBondsMap(Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3)), Map()) == Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3))),
      assert(mergeRedelegatedBondsMap(Map(), Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3))) == Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3))),
      assert(mergeRedelegatedBondsMap(Map("bob" -> Map(1 -> 2, 2 -> 3)), Map("alice" -> Map(1 -> 2, 2 -> 3))) == Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3))),
      assert(mergeRedelegatedBondsMap(Map("bob" -> Map(1 -> 2, 2 -> 3), "tom" -> Map(4 -> 3, 5 -> 6)), Map("tom" -> Map(4 -> 3, 7 -> 6), "alice" -> Map(1 -> 2, 2 -> 3))) == 
                                      Map("alice" -> Map(1 -> 2, 2 -> 3), "bob" -> Map(1 -> 2, 2 -> 3), "tom" -> Map(4 -> 6, 5 -> 6, 7 -> 6))),       
    }

    // The function updateRedelegatedBonded updates a map of redelegated bonds according to a modified bond record.
    // - @param redelegatedBonds a map of redelegated bonds.
    // - @param modified a ModifiedRedelegation record.
    // - @returns an updated map.
    pure def updateRedelegatedBondsMap(redelegatedBonds: RedelegatedBondsMap, modified: ModifiedRedelegation): RedelegatedBondsMap = {
      if (modified.valToModify == "") redelegatedBonds.mapRemoveSet(modified.valsToRemove)
      else {
        val updatedValsToRemoved = modified.valsToRemove.setRemove(modified.valToModify)
        if (modified.epochToModify == -1) redelegatedBonds.mapRemoveSet(updatedValsToRemoved).set(modified.valToModify, redelegatedBonds.get(modified.valToModify).mapRemoveSet(modified.epochsToRemove))
        else {
          val updatedEpochsToRemove = modified.epochsToRemove.setRemove(modified.epochToModify)
          val updatedValBonds = redelegatedBonds.get(modified.valToModify).mapRemoveSet(updatedEpochsToRemove).set(modified.epochToModify, modified.newAmount)
          redelegatedBonds.mapRemoveSet(updatedValsToRemoved).set(modified.valToModify, updatedValBonds)
        }
      }
    }

    run updateRedelegatedBondsMapTest = {
      val redelegatedBonds = Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2))
      val emptyModified = {epoch: -1, valsToRemove: Set(), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedAll = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedValidator = {epoch: 7, valsToRemove: Set("alice"), valToModify: "", epochsToRemove: Set(), epochToModify: -1, newAmount: -1}
      val modifiedValidatorPartial = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "bob", epochsToRemove: Set(1), epochToModify: -1, newAmount: -1}
      val modifiedEpochPartial = {epoch: 7, valsToRemove: Set("alice", "bob"), valToModify: "bob", epochsToRemove: Set(1, 4), epochToModify: 4, newAmount: 1}  
      all {
        assert(updateRedelegatedBondsMap(redelegatedBonds, emptyModified) == redelegatedBonds),
        assert(updateRedelegatedBondsMap(redelegatedBonds, modifiedAll) == Map()),
        assert(updateRedelegatedBondsMap(redelegatedBonds, modifiedValidator) == Map("bob" -> Map(1 -> 1, 4 -> 2))),
        assert(updateRedelegatedBondsMap(redelegatedBonds, modifiedValidatorPartial) == Map("bob" -> Map(4 -> 2))),
        assert(updateRedelegatedBondsMap(redelegatedBonds, modifiedEpochPartial) == Map("bob" -> Map(4 -> 1))),
      }
    }

    // The function updateRedelegatedUnbonded updates an entry of a delegator's redelegated unbonded map.
    // - @param existing a map of redelegated unbonds from starting bonded epoch and ending bonded epoch to RedelegatedBondsMap.
    // - @param redelegatedUnbonds a map from bond starting epoch to RedelegatedBondsMap.
    // - @param end the epoch at which the redelegated bonds being added are withdrawable.
    // - @returns an updated map that includes redelegatedUnbonds.
    pure def updateRedelegatedUnbonded(existing: (Epoch, Epoch) -> RedelegatedBondsMap, redelegatedUnbonds: Epoch -> RedelegatedBondsMap, end: Epoch): (Epoch, Epoch) -> RedelegatedBondsMap = {
      val newTuples =  tuples(redelegatedUnbonds.keys(), Set(end))
      val existingTuples = existing.keys()
      existingTuples.union(newTuples).mapBy(pair => val start = pair._1
                                                    if (pair.in(existingTuples) and pair.in(newTuples)) mergeRedelegatedBondsMap(existing.get(pair), redelegatedUnbonds.get(start))
                                                    else if (pair.in(existingTuples)) existing.get(pair) else redelegatedUnbonds.get(start))
    }

    run updateRedelegatedUnbondedTest = {
      val existing = Map((2, 6) -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)),
                         (2, 5) -> Map("alice" -> Map(1 -> 2, 3 -> 4)),
                         (3, 6) -> Map("bob" -> Map(1 -> 2, 3 -> 4)))
      all {
        assert(updateRedelegatedUnbonded(Map(),Map(), 6) == Map()),
        assert(updateRedelegatedUnbonded(existing, Map(), 6) == existing ),
        assert(updateRedelegatedUnbonded(Map(), Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4))), 6) ==
                                         Map((2, 6) -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)))),
        assert(updateRedelegatedUnbonded(existing, Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4))), 6) ==
                                         Map((2, 6) -> Map("alice" -> Map(1 -> 4, 3 -> 8), "bob" -> Map(1 -> 4, 3 -> 8)),
                                             (2, 5) -> Map("alice" -> Map(1 -> 2, 3 -> 4)),
                                             (3, 6) -> Map("bob" -> Map(1 -> 2, 3 -> 4)))),
      }
    }

    // The function updateTotalRedelegatedUnbonded updates an entry of a delegator's total redelegated unbonded map.
    // - @param existing a map of total redelegated unbonds from starting bonded epoch and source validator to a map of bonds.
    // - @param redelegatedUnbonds a set of redelegated unbonds.
    // - @returns an updated map that includes redelegatedUnbonds.
    pure def updateTotalRedelegatedUnbonded(existing: Epoch -> RedelegatedBondsMap, new: Epoch -> RedelegatedBondsMap): Epoch -> RedelegatedBondsMap = {
      existing.keys().union(new.keys()).mapBy(e => if (existing.has(e) and new.has(e)) mergeRedelegatedBondsMap(existing.get(e), new.get(e))
                                                   else if (existing.has(e)) existing.get(e) else new.get(e))
    }

    run updateTotalRedelegatedUnbondedTest = {
      val existing = Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)),
                         3 -> Map("alice" -> Map(1 -> 2, 3 -> 4)))
      all {
        assert(updateTotalRedelegatedUnbonded(Map(), Map()) == Map()),
        assert(updateTotalRedelegatedUnbonded(existing, Map()) == existing),
        assert(updateTotalRedelegatedUnbonded(Map(), Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)))) ==
                                              Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)))),
        assert(updateTotalRedelegatedUnbonded(existing, Map(2 -> Map("alice" -> Map(1 -> 2, 3 -> 4), "bob" -> Map(1 -> 2, 3 -> 4)))) ==
                                              Map(2 -> Map("alice" -> Map(1 -> 4, 3 -> 8), "bob" -> Map(1 -> 4, 3 -> 8)),
                                                  3 -> Map("alice" -> Map(1 -> 2, 3 -> 4))))
      }
    }

    // The function mergeOutgoingRedelegations updates a validators's outgoing redelegations variable.
    // - @param existing a map of outgoing redelegations.
    // - @param new a new outgoing redelegation.
    // - @param curEpoch the current epoch
    // - @returns an updated map that includes new.
    pure def mergeOutgoingRedelegations(existing: (Epoch, Epoch) -> int, new: Epoch -> int, curEpoch: Epoch): (Epoch, Epoch) -> int = {
      val newTuples = tuples(new.keys(), Set(curEpoch))
      existing.keys().union(newTuples).mapBy(pair => val start = pair._1
                                                     if (existing.has(pair) and pair.in(newTuples)) existing.get(pair) + new.get(start)
                                                     else if (existing.has(pair)) existing.get(pair)
                                                          else new.get(start))
    }

    run mergeOutgoingRedelegationsTest = {
      val existing = Map((2, 6) -> 4,
                         (2, 5) -> 6,
                         (3, 6) -> 3)
      all {
        assert(mergeOutgoingRedelegations(Map(),Map(), 6) == Map()),
        assert(mergeOutgoingRedelegations(existing, Map(), 6) == existing ),
        assert(mergeOutgoingRedelegations(Map(), Map(2 -> 5), 6) == Map((2, 6) -> 5)),
        assert(mergeOutgoingRedelegations(existing, Map(2 -> 5), 6) == Map((2, 6) -> 9, (2, 5) -> 6, (3, 6) -> 3))
      }
    }

    // **************************************************************************
    // Slashing helper functions
    // ************************************************************************* 

    // The function computeSlashableAmount computes how much is left from a bond or unbond after applying a slash given that a set of slashes may have been
    // previously applied.
    // - @param slash the slash record to be applied.
    // - @param initAmount the tokens to be slashed.
    // - @param computeSlashes a map from misbehaving epoch to already computed slashable amount.
    // - @returns an integer with the amount that remains after applying slash constraint to computeSlashes.
    pure def computeSlashableAmount(slash: Slash, initAmount: int, computedSlashes: Epoch -> int): int = {
      val updatedAmount = computedSlashes.keys().filter(x => x + slashProcessingDelay < slash.epoch)
                                                .fold(initAmount, (acc, e) => max(0, acc - computedSlashes.get(e)))
      updatedAmount*slash.rate
    }

    run computeSlashableAmountTest = {
      val initEpoch = 2
      all {
        assert(computeSlashableAmount({epoch: initEpoch + UNBONDING_OFFSET + CUBIC_OFFSET, rate: 1}, 100, Map()) == 100),
        assert(computeSlashableAmount({epoch: initEpoch + UNBONDING_OFFSET + CUBIC_OFFSET + 1, rate: 1}, 100, Map(initEpoch -> 50)) == 50),
        assert(computeSlashableAmount({epoch: initEpoch + UNBONDING_OFFSET + CUBIC_OFFSET, rate: 1}, 100, Map(initEpoch -> 50)) == 100)
      }
    }

    // The function applyListSlashes computes how much remains from an amount of tokens after applying a list of slashes.
    // - @param listSlashes a list of slashes ordered by misbehaving epoch.
    // - @param amount the amount of slashable tokens.
    // - @returns an integer with the amount that remains after applying the list of slashes.
    pure def applyListSlashes(listSlashes: List[Slash], amount: int): int = {
      listSlashes.foldl({finalAmount: amount, computedSlashes: Map()}, (acc, slash) => val slashAmount = computeSlashableAmount(slash, amount, acc.computedSlashes)
                                                                                       {finalAmount: max(0, acc.finalAmount - slashAmount),
                                                                                        computedSlashes: acc.computedSlashes.mapSafeSet(slash.epoch, slashAmount)}).finalAmount
    }

    run applyListSlashesTest = {
      val initEpoch = 2
      val list1 = [{epoch: initEpoch, rate: 1}]
      val list2 = [{epoch: initEpoch, rate: 1}, {epoch: initEpoch+UNBONDING_OFFSET+CUBIC_OFFSET+1, rate: 1} ]
      val list3 = [{epoch: initEpoch, rate: 1},
                   {epoch: initEpoch, rate: 1}]
      val list4 = [{epoch: initEpoch, rate: 1},
                   {epoch: initEpoch, rate: 1},
                   {epoch: initEpoch+UNBONDING_OFFSET+CUBIC_OFFSET+1, rate: 1} ]
      all {
        assert(applyListSlashes([], 100) == 100),
        assert(applyListSlashes(list1, 100) == 0),
        assert(applyListSlashes(list2, 100) == 0),
        assert(applyListSlashes(list3, 100) == 0),
        assert(applyListSlashes(list4, 100) == 0)
      }
    }

    // The function nextSlash compares the slash at the head of two lists and returns the one with smaller
    // misbheaving epoch. It assumes that at least one list has an element.
    // - @param list1 a list of slashes ordered by misbehaving epoch.
    // - @param list2 a second list of slashes ordered by misbehaving epoch.
    // - @returns the slash at the head of any of the lists with smaller misbheaving epoch.

    pure def nextSlash(list1: List[Slash], list2: List[Slash]): (Slash, List[Slash], List[Slash]) = {
      if (list1 == List()) (head(list2), list1, tail(list2))
      else if (list2 == List()) (head(list1), tail(list1), list2)
           else if (head(list1).epoch <= head(list2).epoch) (head(list1), tail(list1), list2)
                else (head(list2), list1, tail(list2))
    }
    
    run nextSlashTest = {
      val slash = {epoch: 0, rate: 1}
      val list1 = [slash.with("epoch", 1),
                   slash.with("epoch", 6),
                   slash.with("epoch", 9)]
      val list2 = [slash.with("epoch", 2),
                   slash.with("epoch", 6),
                   slash.with("epoch", 8)]
      all {
        assert(nextSlash(List(), List(slash.with("epoch", 1))) == (slash.with("epoch", 1), List(), List())),
        assert(nextSlash(List(slash.with("epoch", 1)), List()) == (slash.with("epoch", 1), List(), List()))
      }
    }

    // The function mergeListSlashes merges two lists of slashes ordered by misbehaving epoch.
    // - @param list1 a list of slashes ordered by misbehaving epoch.
    // - @param list2 a second list of slashes ordered by misbehaving epoch.
    // - @returns a third list of slashes including all elements in both imput lists ordered by misbehaving epoch.
    pure def mergeListSlashes(list1: List[Slash], list2: List[Slash]): List[Slash] = {
      val sumLength = length(list1) + length(list2)
      if (sumLength == 0) List()
      else 1.to(sumLength).fold(([], list1, list2), (acc, _) => val result = nextSlash(acc._2, acc._3)
                                                                (acc._1.append(result._1), result._2, result._3))._1
    }

    run mergeListSlashesTest = all {
      val slash = {epoch: 0, rate: 1}
      val list1 = [slash.with("epoch", 1),
                   slash.with("epoch", 6),
                   slash.with("epoch", 9)]
      val list2 = [slash.with("epoch", 2),
                   slash.with("epoch", 6),
                   slash.with("epoch", 8)]
      val resultMerge = [slash.with("epoch", 1),
                         slash.with("epoch", 2),
                         slash.with("epoch", 6),
                         slash.with("epoch", 6),
                         slash.with("epoch", 8),
                         slash.with("epoch", 9)]
      all {
        assert(mergeListSlashes(list1, list2) == resultMerge),
        assert(mergeListSlashes(list2, list1) == resultMerge),
        assert(mergeListSlashes(List(), List()) == List()),
        assert(mergeListSlashes(list1, List()) == list1),
        assert(mergeListSlashes(List(), list2) == list2)
      }
    }
    
    // The function foldRedelegatedBonds iterates over a RedelegatedBondsMap and computes the both the sum of all rdelegated tokens and
    //  how much is left after applying all relevant slashes.
    // - @param bonds a RedelegatedBondsMap.
    // - @param start the epoch at which the redelegated bonds were effectively bonded.
    // - @param listSlashes a list of slashes to be applied to the redelegated bonds.
    // - @param slashes a map from validator address to list of slashes.
    // - @returns the total amount of redelegated tokens and the total amount after slashing.
    pure def foldRedelegatedBonds(bonds: RedelegatedBondsMap, start: Epoch, listSlashes: List[Slash], slashes: Address -> List[Slash]): {totalRedelegated: int, totalAfterSlashing: int} = {
      bonds.keys().fold({totalRedelegated: 0, totalAfterSlashing: 0},
                        (accSrc, src) => bonds.get(src).keys().fold(accSrc,
                                                                    (accEpoch, redBondStart) => val selectList = slashes.get(src).select(slash => inRedelegationSlashingWindow(slash.epoch, startRedelegationFromEnd(start), start) and
                                                                                                                                                  redBondStart <= slash.epoch)
                                                                                                val mergedList = mergeListSlashes(listSlashes, selectList)
                                                                                                {totalRedelegated: accEpoch.totalRedelegated + bonds.get(src).get(redBondStart),
                                                                                                totalAfterSlashing: accEpoch.totalAfterSlashing + applyListSlashes(mergedList, bonds.get(src).get(redBondStart))}))
    }

    run foldRedelegatedBondsTest = {
      val allValidators = Set("alice", "bob")
      val start = 7
      val redelegatedBonds = Map("alice" -> Map(2 -> 1, 4 -> 1), "bob" -> Map(1 -> 1, 4 -> 2))
      all {
        assert(foldRedelegatedBonds(redelegatedBonds, start, List(), allValidators.mapBy(x => List())) == {totalRedelegated: 5, totalAfterSlashing: 5}),
        assert(foldRedelegatedBonds(redelegatedBonds, start, List({epoch: 0, rate: 1}), allValidators.mapBy(x => List())) == {totalRedelegated: 5, totalAfterSlashing: 0}),
        assert(foldRedelegatedBonds(redelegatedBonds, start, List(), allValidators.mapBy(x => if (x=="alice") List({epoch: 6, rate: 1}) else List())) == {totalRedelegated: 5, totalAfterSlashing: 3}),
      }
    }

    // The function computeAmountAfterSlashingUnbond computes from a set of unbonds (both redelegated and not) how much is left after applying all relevant
    // slashes.
    // - @param unbonds a set of unbonds: a map from bond starting epoch and unbond ending epoch to amount of tokens.
    // - @param redelegatedUnbonds a set of redelegated unbonds: a map from bonds tarting epoch to RedelegatedBondsMap.
    // - @param validator the address of the validator from which the the bonds have been unbonded.
    // - @param slashes a map from validator address to list of slashes.
    // - @returns the total amount after slashing and a map from bond starting epoch to amount after slashing.
    pure def computeAmountAfterSlashingUnbond(unbonds: (Epoch, Epoch) -> int, redelegatedUnbonds: Epoch -> RedelegatedBondsMap, validator: Address, slashes: Address -> List[Slash]): {sum: int, epochMap: Epoch -> int} = {
      val initMap = unbonds.keys().map(pair => pair._1).mapBy(e => 0)
      unbonds.keys().fold({sum: 0, epochMap: initMap}, (acc, unbondKey) => val start = unbondKey._1
                                                                           val listSlashes = slashes.get(validator).select(slash => start <= slash.epoch)
                                                                           val resultFold = if (redelegatedUnbonds.has(start)) foldRedelegatedBonds(redelegatedUnbonds.get(start), start, listSlashes, slashes)
                                                                                            else {totalRedelegated: 0, totalAfterSlashing: 0}
                                                                           val totalNoRedelegated = unbonds.get(unbondKey) - resultFold.totalRedelegated
                                                                           val afterNoRedelegated = applyListSlashes(listSlashes, totalNoRedelegated)
                                                                           val amountAfterSlashing = afterNoRedelegated + resultFold.totalAfterSlashing
                                                                           {sum: acc.sum + amountAfterSlashing,
                                                                            epochMap: acc.epochMap.set(start, amountAfterSlashing)})
    }
    
    run computeAmountAfterSlashingUnbondTest = {
      val allValidators = Set("alice", "bob")
      val unbonds = Map((2, 6) -> 5, (4, 6) -> 6)
      val redelegatedBonds = Map(2 -> Map("alice" -> Map(1 -> 1)))
      all {
        assert(computeAmountAfterSlashingUnbond(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => List())) == {sum: 11, epochMap: Map(2 -> 5, 4 -> 6)}),
        assert(computeAmountAfterSlashingUnbond(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="bob") List({epoch: 5, rate: 1}) else List())) == {sum: 0, epochMap: Map(2 -> 0, 4 -> 0)}),
        assert(computeAmountAfterSlashingUnbond(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="alice") List({epoch: 0, rate: 1}) else List())) == {sum: 11, epochMap: Map(2 -> 5, 4 -> 6)}),
        assert(computeAmountAfterSlashingUnbond(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="alice") List({epoch: 1, rate: 1}) else List())) == {sum: 10, epochMap: Map(2 -> 4, 4 -> 6)})
      }
    }

    // The function computeAmountAfterSlashingWithdraw computes from a set of unbonds (both redelegated and not) how much is left after applying all relevant
    // slashes.
    // - @param unbonds a set of unbonds: a map from bond starting epoch and unbond ending epoch to amount of tokens.
    // - @param redelegatedUnbonds a set of redelegated unbonds: a map from bonds tarting epoch to RedelegatedBondsMap.
    // - @param validator the address of the validator from which the the bonds have been unbonded.
    // - @param slashes a map from validator address to list of slashes.
    // - @returns the total amount after slashing and a map from bond starting epoch to amount after slashing.
    pure def computeAmountAfterSlashingWithdraw(unbonds: (Epoch, Epoch) -> int, redelegatedUnbonds: (Epoch, Epoch) -> RedelegatedBondsMap, validator: Address, slashes: Address -> List[Slash]): {sum: int, epochMap: Epoch -> int} = {
      val initMap = unbonds.keys().map(pair => pair._1).mapBy(e => 0)
      unbonds.keys().fold({sum: 0, epochMap: initMap}, (acc, unbondKey) => val start = unbondKey._1
                                                                           val end = unbondKey._2
                                                                           val listSlashes = slashes.get(validator).select(slash => start <= slash.epoch and
                                                                                                                           end - UNBONDING_OFFSET - CUBIC_OFFSET > slash.epoch)
                                                                           val resultFold = if (redelegatedUnbonds.has(unbondKey)) foldRedelegatedBonds(redelegatedUnbonds.get(unbondKey), start, listSlashes, slashes)
                                                                                            else {totalRedelegated: 0, totalAfterSlashing: 0}
                                                                           val totalNoRedelegated = unbonds.get(unbondKey) - resultFold.totalRedelegated
                                                                           val afterNoRedelegated = applyListSlashes(listSlashes, totalNoRedelegated)
                                                                           val amountAfterSlashing = afterNoRedelegated + resultFold.totalAfterSlashing
                                                                           {sum: acc.sum + amountAfterSlashing,
                                                                            epochMap: acc.epochMap.set(start, amountAfterSlashing)})
    }

    run computeAmountAfterSlashingWithdrawTest = {
      val allValidators = Set("alice", "bob")
      val unbonds = Map((2, 20) -> 5, (4, 20) -> 6)
      val redelegatedBonds = Map((2, 20) -> Map("alice" -> Map(1 -> 1)))
      all {
        assert(computeAmountAfterSlashingWithdraw(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => List())) == {sum: 11, epochMap: Map(2 -> 5, 4 -> 6)}),
        assert(computeAmountAfterSlashingWithdraw(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="bob") List({epoch: 5, rate: 1}) else List())) == {sum: 0, epochMap: Map(2 -> 0, 4 -> 0)}),
        assert(computeAmountAfterSlashingWithdraw(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="alice") List({epoch: 0, rate: 1}) else List())) == {sum: 11, epochMap: Map(2 -> 5, 4 -> 6)}),
        assert(computeAmountAfterSlashingWithdraw(unbonds, redelegatedBonds, "bob", allValidators.mapBy(x => if (x=="alice") List({epoch: 1, rate: 1}) else List())) == {sum: 10, epochMap: Map(2 -> 4, 4 -> 6)})
      }
    }

    // The function computeTotalUnbonded computes the total amount of tokens unbonded from a validator that were contributing to the validator's stake when this misbehaved at
    // a previous epoch, after applying a set of relevant slashes.
    // - @param validator the misbehaving validator's address.
    // - @param infractionEpoch the epoch at which the validator misbehaved.
    // - @param slashes a map from validator address to a list of already processed slashes.
    // - @param totalUnbonded a map of bonds from epoch to amount of tokens from which the final amount is computed.
    // - @param totalRedelegatedUnbonded a map of redelegated bonds from epoch to RedelegatedBondsMap.
    // - @returns an integer with the amount of tokens that were contributing to the validator at the misbehaving epoch that have been unbonded.
    pure def computeTotalUnbonded(validator: Address, infractionEpoch: Epoch, slashes: Address -> List[Slash], totalUnbonded: Epoch -> int, totalRedelegatedUnbonded: Epoch -> RedelegatedBondsMap): int = {
      val epochs = totalUnbonded.keys().filter(e => e <= infractionEpoch and totalUnbonded.get(e) > 0)
      epochs.fold(0, (sum, e) => val listSlashes = slashes.get(validator).select(s => e <= s.epoch and s.epoch + slashProcessingDelay < infractionEpoch)
                                 val filteredSlashMap = slashes.keys().mapBy(v => slashes.get(v).select(s => s.epoch + slashProcessingDelay < infractionEpoch))
                                 val resultFold = if (totalRedelegatedUnbonded.has(e)) foldRedelegatedBonds(totalRedelegatedUnbonded.get(e), e, listSlashes, filteredSlashMap)
                                                  else {totalRedelegated: 0, totalAfterSlashing: 0}
                                 val totalNoRedelegated = totalUnbonded.get(e) - resultFold.totalRedelegated
                                 val afterNoRedelegated = applyListSlashes(listSlashes, totalNoRedelegated)
                                 val amountAfterSlashing = afterNoRedelegated + resultFold.totalAfterSlashing
                                 sum + amountAfterSlashing)
    }

    run computeTotalUnbondedTest = {
      val allValidators = Set("alice", "bob")
      val totalUnbonded = Map(2 -> 5, 8 -> 20)
      val totalRedelegateUnbonded = Map(8 -> Map("bob" -> Map(4 -> 10)))
      all {
        assert(computeTotalUnbonded("alice", 10, allValidators.mapBy(v => List()), totalUnbonded, totalRedelegateUnbonded) == 25),
        assert(computeTotalUnbonded("alice", 7, allValidators.mapBy(v => List()), totalUnbonded, totalRedelegateUnbonded) == 5),
        assert(computeTotalUnbonded("alice", 10, allValidators.mapBy(v => if (v == "alice") List({epoch: 2, rate: 1}) else List()), totalUnbonded, totalRedelegateUnbonded) == 20),
        assert(computeTotalUnbonded("alice", 10, allValidators.mapBy(v => if (v == "alice") List({epoch: 2, rate: 1}) else List({epoch: 4, rate: 1})), totalUnbonded, totalRedelegateUnbonded) == 10),
      }
    }

    // Computes the total amount of tokens unbonded by a validator that were bonded after this misbehaved at a given epoch
    // - @param infractionEpoch the misbehaving epoch.
    // - @param totalUnbonded the set of unbonded tokens in a map from bond starting epoch to amount of tokens.
    // - @returns an integer with the amount of tokens unbonded.
    pure def computeRecentTotalUnbonded(infractionEpoch: Epoch, totalUnbonded: Epoch -> int): int = {
      val epochs = totalUnbonded.keys().filter(e => e > infractionEpoch and totalUnbonded.get(e) > 0)
      epochs.fold(0, (sum, e) => sum + totalUnbonded.get(e))
    }

    run computeRecentTotalUnbondedTest = all {
      assert(computeRecentTotalUnbonded(5, Map()) == 0),
      assert(computeRecentTotalUnbonded(5, Map(6 -> 10, 7 -> 20)) == 30),
      assert(computeRecentTotalUnbonded(5, Map(4 -> 10, 7 -> 20)) == 20),
      assert(computeRecentTotalUnbonded(8, Map(4 -> 10, 7 -> 20)) == 0),
    }

    // Returns the slahs rate depending of the type of infraction
    pure def minSlashRate(infraction: str): Dec = {
      if (infraction == "duplicate_vote") DUPLICATE_RATE else LIGHT_RATE
    }

    // Computes a slash rate based on a set of slashes
    // - @param setSlashes a set of slashes
    // - @returns an integer represting the slash rate
    pure def computeFinalRate(setInfractions: Set[Infraction]): int = {
      1
    } 

        // Computes for a given validator and a slash how it much should be slashed at all epochs between the current epoch (curEpoch) + 1 and the current epoch + 1 + 
    // PIPELINE_OFFSET, accounting for any tokens already unbonded.
    pure def slashValidator(validator: Address,
                            initMap: Epoch -> int,
                            stakes: Epoch -> int,
                            curEpoch: Epoch,
                            infractionStake: int,
                            slashes: Address -> List[Slash],
                            totalUnbonded: Epoch -> Epoch -> int,
                            totalRedelegatedUnbonded: Epoch -> Epoch -> RedelegatedBondsMap,
                            totalBonded: Epoch -> int,
                            finalRate: int): Epoch -> int = {
      val infractionEpoch = curEpoch - slashProcessingDelay
      val initTotalUnbonded = (infractionEpoch+1).to(curEpoch).fold(0, (sum, e) => sum + computeTotalUnbonded(validator, infractionEpoch, slashes, totalUnbonded.get(e), totalRedelegatedUnbonded.get(e)))
      val initBalanceBonds = (infractionEpoch+1).to(curEpoch).fold(0, (sum, e) => sum +(totalBonded.get(e) - computeRecentTotalUnbonded(infractionEpoch, totalUnbonded.get(e))))
      val result = (curEpoch+1).to(curEpoch+PIPELINE_OFFSET).fold((initTotalUnbonded, initBalanceBonds, initMap), (acc, e) => val updatedTotalUnbonded = acc._1 + computeTotalUnbonded(validator, infractionEpoch, slashes, totalUnbonded.get(e), totalRedelegatedUnbonded.get(e))
                                                                                                                              val updatedBalanceBonds = acc._2 + (totalBonded.get(e) - computeRecentTotalUnbonded(infractionEpoch, totalUnbonded.get(e)))
                                                                                                                              val slashedAmount = (infractionStake - updatedTotalUnbonded) * finalRate
                                                                                                                              val currentStake = stakes.get(e) - acc._3.get(e)
                                                                                                                              val slashableStake = (currentStake - updatedBalanceBonds)
                                                                                                                              (updatedTotalUnbonded, updatedBalanceBonds, acc._3.set(e, acc._3.get(e) + min(slashedAmount, slashableStake))))
      result._3
    }

    pure def hasRedelegation(mapRedelegations: Epoch -> RedelegatedBondsMap, redBondStart: Epoch, validator: Address, bondStart: Epoch): bool = {
      if (mapRedelegations.has(redBondStart))
        if (mapRedelegations.get(redBondStart).has(validator)) 
          if (mapRedelegations.get(redBondStart).get(validator).has(bondStart)) true
          else false
        else false
      else false
    }

    pure def slashRedelegation(amount: int,
                               bondStart: Epoch,
                               redBondStart: Epoch,
                               srcValidator: Address,
                               curEpoch: Epoch,
                               slashes: List[Slash],
                               totalRedelegatedUnbonded: Epoch -> Epoch -> RedelegatedBondsMap,
                               finalRate: int,
                               slashedAmountsMap: Epoch -> int): Epoch -> int = {
      val infractionEpoch = curEpoch - slashProcessingDelay
      val initTotalUnbonded = (infractionEpoch+1).to(curEpoch).fold(0, (sum, e) => if (not(totalRedelegatedUnbonded.get(e).hasRedelegation(redBondStart, srcValidator, bondStart))) sum
                                                                                   else sum + totalRedelegatedUnbonded.get(e).get(redBondStart).get(srcValidator).get(bondStart))
      val result = (curEpoch+1).to(curEpoch+PIPELINE_OFFSET).fold((initTotalUnbonded, slashedAmountsMap), (acc, e) => val updatedTotalUnbonded = if (not(totalRedelegatedUnbonded.get(e).hasRedelegation(redBondStart, srcValidator, bondStart))) acc._1
                                                                                                                                                 else acc._1 + totalRedelegatedUnbonded.get(e).get(redBondStart).get(srcValidator).get(bondStart)
                                                                                                                      val slashAmount = val listSlashes = slashes.select(s => inRedelegationSlashingWindow(s.epoch, startRedelegationFromEnd(e), e) and
                                                                                                                                                                              s.epoch + slashProcessingDelay < infractionEpoch and
                                                                                                                                                                              bondStart <= s.epoch)
                                                                                                                                        applyListSlashes(listSlashes, amount - updatedTotalUnbonded) * finalRate
                                                                                                                      val slashableStake = val listSlashes = slashes.select(s => inRedelegationSlashingWindow(s.epoch, startRedelegationFromEnd(e), e) and
                                                                                                                                                                                 bondStart <= s.epoch)
                                                                                                                                           applyListSlashes(listSlashes, amount - updatedTotalUnbonded)
                                                                                                                      (updatedTotalUnbonded, acc._2.set(e, acc._2.get(e) + min(slashAmount, slashableStake))))
      result._2                                                                                                                                  
    }

    run slashRedelegationTest = {
      val totalRedelegatedUnbonded = Map(10 -> Map(), 11 -> Map(), 12 -> Map(), 13 -> Map(10 -> Map("alice" -> Map(7 -> 2))), 14 -> Map(), 15 -> Map(), 16 -> Map(), 9 -> Map())
      val slashedAmountsMap = Map(15 -> 0, 16 -> 0)
      all {
        assert(slashRedelegation(7, 7, 10, "alice", 14, [], totalRedelegatedUnbonded, 1, slashedAmountsMap) == Map(15 -> 5, 16 -> 5))
      }
    }

    pure def slashValidatorRedelegation(srcValidator: Address,
                                        curEpoch: Epoch,
                                        redelegations: (Epoch, Epoch) -> int,
                                        slashes: List[Slash],
                                        totalRedelegatedUnbonded: Epoch -> Epoch -> RedelegatedBondsMap,
                                        finalRate: int,
                                        slashedAmountsMap: Epoch -> int): Epoch -> int = {
      val infractionEpoch = curEpoch - slashProcessingDelay
      redelegations.keys().fold(slashedAmountsMap, (acc, pairEpochs) => val bondStart = pairEpochs._1
                                                                        val redelegationStart = pairEpochs._2
                                                                        if (inRedelegationSlashingWindow(infractionEpoch, redelegationStart, endRedelegationFromStart(redelegationStart)) and                         
                                                                            bondStart <= infractionEpoch) slashRedelegation(redelegations.get(pairEpochs),
                                                                                                                            bondStart,
                                                                                                                            endRedelegationFromStart(redelegationStart),
                                                                                                                            srcValidator,
                                                                                                                            curEpoch,
                                                                                                                            slashes,
                                                                                                                            totalRedelegatedUnbonded,
                                                                                                                            finalRate,
                                                                                                                            acc) 
                                                                        else acc)                                   
    }

    run slashValidatorRedelegationTest = {
      val redelegations = Map((7, 8) -> 7)
      val totalRedelegatedUnbonded = Map(10 -> Map(), 11 -> Map(), 12 -> Map(), 13 -> Map(10 -> Map("alice" -> Map(7 -> 2))), 14 -> Map(), 15 -> Map(), 16 -> Map(), 9 -> Map())
      val slashedAmountsMap = Map(15 -> 0, 16 -> 0)
      all {
        assert(slashValidatorRedelegation("alice", 14, redelegations, [], totalRedelegatedUnbonded, 1, slashedAmountsMap) == Map(15 -> 5, 16 -> 5))
      }
    }
}
module stack
sig item {}

// contains all elements which is not in Stack
one sig DataManager {
	var freeElems: set item
}

// Head points to the next node by Next
one sig Stack {
	var Head: one item,
	var Next: item -> item,
}

fun v_next : item->item { Stack.Next }
fun v_head  : one item { Stack.Head }

pred pop {
	--prereq
		#v_head.*v_next > 1
		StackIsValid

	--action
		DataManager.freeElems' = DataManager.freeElems + v_head
		v_head' = v_head.v_next
		v_head'.v_next' = v_head'.v_next

	--postreq
		no v_head.v_next'
		all i: item - v_head' | i.v_next' = i.v_next
		StackIsValid
}

pred push[e: item] {
	--prereq
		e in DataManager.freeElems
		StackIsValid

	--action
		DataManager.freeElems' = DataManager.freeElems - e
		v_head' = e
		v_head'.v_next' = v_head

	--postreq
		v_head.v_next' = v_head.v_next
		all i: item - v_head' | i.v_next' = i.v_next
		StackIsValid
}

pred clear{ 
	--prereq
		StackIsValid

	--action
		// place each element to DataManager
		all i: item - v_head | i in DataManager.freeElems' 
		//    expect header
		DataManager.freeElems' = item - v_head

	--postreq
		all i : DataManager.freeElems' | no i.v_next'
		v_head' = v_head
		no v_head'.v_next'
		StackIsValid
}

// HELPER FUNCTIONS
//=------------------------------------------------------------------------------------------------
// check that e is reachable from n (in terms of one-connected list)
pred reachable[n: item, e: item] {
	e in n.*v_next
}
// check that e is in the Stack
pred stackContainsElement(e: item) {
    e = v_head or reachable[v_head, e]
}

// Helper action: nop
pred noChange { all i:item {i.v_next' = i.v_next && DataManager.freeElems'=DataManager.freeElems && v_head' = v_head} }
// Set of transactions
pred transitions {
	pop or (some e: item | push[e]) or clear or noChange
}
//=------------------------------------------------------------------------------------------------

pred StackIsValid {
	// header is fake node (to simplify realization)
	one v_head

	v_head not in DataManager.freeElems
	// elements from stack can't be in freeElems
	all i: v_head.*v_next | i not in DataManager.freeElems
	
	// union of sets is complete
	all i: item | stackContainsElement[i] or i in DataManager.freeElems

	// disconect free elements 
	all i: DataManager.freeElems | no i.v_next

	// Acyclicity
	// NOTE: 'iff not' is XOR
	all disj i,j: v_head.*v_next | reachable[i, j] iff not reachable[j, i]

	// Check linearity
	all disj i,j: v_head.*v_next | i.v_next != j.v_next
	all i: v_head.*v_next | v_head != i.v_next

	// check connections
	all i: v_head.*v_next | no i.v_next or one i.v_next
	all i: v_head.*v_next | no i.v_next or i.v_next not in DataManager.freeElems
}

fact "init" {
	#item > 6
	#v_head.*v_next > 3
	StackIsValid
}

run {
	always transitions
} for 12 but 1..10 steps

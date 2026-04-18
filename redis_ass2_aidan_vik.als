// =============================================================================
// SWEN90010 Assignment 2 — Redis/ChatGPT Data Leakage Model
// =============================================================================
//
// Student 1: [Aidan Butler, 1353349]
// Student 2: [Name, Student ID]
//
// =============================================================================

// Debugging: each action predicate records which action was last performed,
// to make it easier to interpret traces produced by Alloy.
// The correspondence between Action values and predicates is:
//   DoNothing           -> do_nothing
//   UserSendReq         -> action_user_send_http_request
//   UserRecvResp        -> action_user_recv_http_response
//   RecvReqAcquireConn  -> action_recv_http_request_and_acquire_connection
//   RedisProcess        -> action_redis_process_connection
//   ReleaseConnSendResp -> action_release_connection_and_send_http_response
//   RequestCancelled    -> action_user_request_cancelled
abstract sig Action {}
one sig DoNothing, UserSendReq, UserRecvResp, RecvReqAcquireConn,
              RedisProcess, ReleaseConnSendResp, RequestCancelled extends Action {}

// Data is the abstract type of all data in the system.
// UserData represents data that belongs to a specific user.
// DataRequestCancelled is a special sentinel value used to inform
// a user that their request was cancelled.
abstract sig Data {}
sig UserData extends Data {}
one sig DataRequestCancelled extends Data {}

// Each User has a set of UserData items that belong to them.
sig User {
  my_data : set UserData
}

// Task 1a: Write a predicate user_data_disjoint that expresses the property
// that no two different users share any data items. Test it, then promote
// it to a fact.

// FILL IN HERE

//Take two users from set of all users, ensuring they are disjoint, and check if 
//their sets of personal data intersect
pred user_data_disjoin{
	all disj u1, u2 : User | no (u1.my_data & u2.my_data)
}

//Runs the predicate above with a scope of 3 using exactly 2 users
//Returning predcate is consistent when ran
run user_data_disjoin for 3 but exactly 2 User

//Moved the predicate above that has now been tested into a fact named disjoint
fact disjoint {
	user_data_disjoin
}


// HTTP messages carry Data as their contents.
// An HTTPRequest is sent by a user (src) to the server.
// An HTTPResponse is sent by the server to a user (dest).
abstract sig HTTPMessage {
  contents : Data
}

sig HTTPResponse extends HTTPMessage {
  dest : User
}

sig HTTPRequest extends HTTPMessage {
  src : User
}

// Connections model the Redis connection pool. Each connection can be
// allocated to at most one user at a time and has separate send/recv
// data buffers for communicating with the Redis backend.
sig Connection {}

// The State records the current state of the entire system.
// http_network: holds at most one HTTP message in transit between users and the server.
// connection_send_data: for each connection, the user data being sent to Redis.
// connection_recv_data: for each connection, the user data received back from Redis.
// connection_for: records which user (if any) each connection is currently allocated to.
// last_action: records the most recent action, for debugging/trace readability.
one sig State {
  var http_network : lone HTTPMessage,
  var connection_send_data : Connection -> lone UserData,
  var connection_recv_data : Connection -> lone UserData,
  var connection_for : Connection -> lone User,
  var last_action : Action
}

// When BugFixed is present, the bug fix is enabled.
// When BugFixed is absent, the system exhibits the vulnerable behaviour.
lone sig BugFixed {}

// Task 1b: Complete the Init predicate.
pred Init {
  // FILL IN HERE
	//Just ensures that all sets are empty, and the last_action is set to DoNothing
	no State.http_network 
       no State.connection_send_data + State.connection_recv_data + State.connection_for
	State.last_action = DoNothing
}

// Task 1c: Complete the action_user_send_http_request predicate.
//Update the predicate to contain two arguments, one specifying the user, and
//One specifing the data to be send
pred action_user_send_http_request[u: User, d: UserData] {
  // FILL IN HERE
	//HTTP network is currently empty
	no State.http_network
	//User must own the data they are sending
	d in u.my_data
	//Need to create a new HTTPRequest and assign it to the next http_network
	one req: HTTPRequest | {
		req.contents = d
		req.src = u
		State.http_network' = req
	}
	//Update Last action	
	State.last_action' = UserSendReq
	//Everything else remaind unchanged
	State.connection_for' = State.connection_for
	State.connection_send_data' = State.connection_send_data
	State.connection_recv_data' = State.connection_recv_data
}

// Task 1d: Complete the action_user_recv_http_response predicate.
pred action_user_recv_http_response {
  // FILL IN HERE
	//Ensure there is a HTTPResponse in the http_network that is being sent to some user
	some u: User | {
		State.http_network in HTTPResponse
		State.http_network.dest = u
	//Once completed, the message is removed
	no State.http_network'
	//Last action updated
	State.last_action' = UserRecvResp
	//Ensure other states remain unchanged
	State.connection_for' = State.connection_for
	State.connection_send_data' = State.connection_send_data
	State.connection_recv_data' = State.connection_recv_data
}

// Task 1e: Complete the action_recv_http_request_and_acquire_connection predicate.
pred action_recv_http_request_and_acquire_connection {
  // FILL IN HERE
	//Identify that there is a message in the network that is a request
	State.http_network in HTTPRequest
	//find a connection that isnt mapped to any user in State.connection_for
	some c: Connection | {
		no State.connection_for[c]
		//Ensure network is cleared for next state
		no State.http_network'
		//Allocate the connection and write the data
		State.connection_for' = State.connection_for ++ (c -> State.http_network.src)
		State.connection_send_data' = State.connection_send_data ++ (c -> State.http_network.contents)
		//Update Last Action
		State.last_action' = RecvReqAcquireConn
		//Ensure other states remain unchanged
		State.connection_recv_data' = State.connection_recv_data
	}

}

// Task 1f: Complete user_data_for_same_user and action_redis_process_connection.
pred user_data_for_same_user[d, d2 : UserData] {
  // FILL IN HERE
}

pred action_redis_process_connection {
  // FILL IN HERE
}

// Task 1g: Complete the action_release_connection_and_send_http_response predicate.
pred action_release_connection_and_send_http_response {
  // FILL IN HERE
}

// Task 1h: Complete the action_user_request_cancelled predicate.
pred action_user_request_cancelled {
  // FILL IN HERE
}

// Given: do_nothing predicate (do not modify)
pred do_nothing {
  State.http_network' = State.http_network
  State.connection_for' = State.connection_for
  State.connection_recv_data' = State.connection_recv_data
  State.connection_send_data' = State.connection_send_data
  State.last_action' = DoNothing
}

// Given: Init is the initial state (do not modify)
fact Init_is_Initial {
  Init
}

// Given: transition relation (do not modify)
fact trans {
  always (do_nothing or action_user_request_cancelled or
              action_release_connection_and_send_http_response or
              action_redis_process_connection or
              action_recv_http_request_and_acquire_connection or
              action_user_recv_http_response or
              action_user_send_http_request[User, UserData])
}

// =============================================================================
// Task 2: Discover the Vulnerability
// =============================================================================

// Task 2a: Write your NoDataLeak assertion and check command here.

// FILL IN HERE


// Task 2b: Write your vulnerability run command here, with comments explaining
// the sequence of events and why the vulnerability arises.

// FILL IN HERE


// =============================================================================
// Task 3: Diagnose the Root Cause
// =============================================================================

// Task 3a: Write your inv predicate and check command here.

// FILL IN HERE


// Task 3b: Write a comment explaining (i) which action predicate causes
// the invariant to be violated and what it fails to do, and (ii) how
// the resulting violation enables the data leakage vulnerability.

// FILL IN HERE


// =============================================================================
// Task 4: Fix and Verify
// =============================================================================

// Task 4a: Using your analysis from Task 3, modify the action predicate
// (above) that is the root cause of the vulnerability to fix the problem.
// Use the BugFixed sig as a guard (see the assignment spec for details).
// (No new code goes here — modify the predicate definition above.)

// Task 4b: Write check commands to verify that when some BugFixed,
// NoDataLeak holds and inv is maintained.

// FILL IN HERE


// Task 4c(i): Discuss your choice of bounds for the verification checks
// in Task 4b. What behaviours are covered? What confidence does a
// successful check provide? What are the limitations of bounded verification?

// FILL IN HERE


// Task 4c(ii): Identify at least one simplification or abstraction in this
// model that could mean a real-world vulnerability goes undetected, and
// explain concretely what kind of vulnerability or behaviour it could miss.

// FILL IN HERE

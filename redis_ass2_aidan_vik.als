// =============================================================================
// SWEN90010 Assignment 2 — Redis/ChatGPT Data Leakage Model
// =============================================================================
//
// Student 1: [Name, Student ID]
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
fact user_data_disjoint {
	 always all disj u1, u2: User | no (u1.my_data & u2.my_data) 
	//all u1: user | no some userB: user | userA.Data = userB.Data & userA != userB}
}

// TODO:  fill in the run command


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
	no State.http_network
	no State.connection_send_data
	no State.connection_recv_data
	no State.connection_for
	no State.last_action
// all variable fiields is empty
// last action is DoNothing
}


// Task 1c: Complete the action_user_send_http_request predicate.
pred action_user_send_http_request {
// A User sends an HTTPRequest onto the http network. 

	//pre condition
	// there is a user, with data, -- does this contrain only one?
	some u: User, d: UserData {
		// data is theirs
		d in u.my_data

		//network is empty
		no State.http_network

		//find httpreq

		some req: HTTPRequest | req.src in u & req.contents = d {
			State.http_network' = req
		}
		
		//rest unchanged
		State.connection_for' = State.connection_for
		State.connection_recv_data' = State.connection_recv_data
		State.connection_send_data' = State.connection_send_data

		//update action
		State.last_action' = UserSendReq
	}
}

// Task 1d: Complete the action_user_recv_http_response predicate.
pred action_user_recv_http_response  {
// A User receives an HTTPResponse that is currently on the http network and is destined for that User. The message is removed from the network.

	 some msg: State.http_network, u: User | {

	// precondition 
	//http_network has a HTTP Response,
	msg in HTTPResponse

	// destined for that User
	msg.dest = u


	// post condition 
	// send data to user, as not explicitly stated - might REMOVE
	u.my_data' = u.my_data + msg.contents

	// remove response
	State.http_network' = none
	
	//unchanged. 
 	State.connection_for' = State.connection_for
	State.connection_recv_data' = State.connection_recv_data
	State.connection_send_data' = State.connection_send_data

	//update action
	State.last_action' = UserRecvResp
	}

}

// Task 1e: Complete the action_recv_http_request_and_acquire_connection predicate.
pred action_recv_http_request_and_acquire_connection {
  // FILL IN HERE

// The web frontend receives an HTTPRequest from the http network and removes
//it from the network, acquires a Connection that is not currently allocated to any User,
//records in connection for that the Connection is now allocated to the request’s sender,
//and writes the request’s contents to the Connection’s connection send data buffer.


	// precondition

	some req: State.http_network, conn: Connection | {

		// req is request
		req in HTTPRequest

		// acquires free connection (i.e not allocated to any user. )
		no State.connection_for[conn]

		// post condition
		State.connection_for' = State.connection_for + (conn -> req.src)

		// writes the request’s contents to the Connection’s connection send data buffer. -- potentish BUG?
		State.connection_send_data' = State.connection_send_data + (conn -> req.contents)

	}

	// remove request
	State.http_network' = none

	//unchanged
	State.connection_recv_data' = State.connection_recv_data
	
	// update action
	State.last_action' = RecvReqAcquireConn

}

// Task 1f: Complete user_data_for_same_user and action_redis_process_connection.
pred user_data_for_same_user[d, d2 : UserData] {
  // FILL IN HERE

	// basically, check that the connection number matches the user, for both send and receive data, 
	// dont know if its true that d2 is not in user.mydata, but d is definitely in it. 
	some u: User | (d + d2) in u.my_data
}

pred action_redis_process_connection {
  // , which occurs when there is data in a Connection’s “send data” buffer, in which case the data is removed from that buffer 
// and some other data is written to the same channel’s “recv data” buffer. 
// The data written to the “recv data” buffer belongs to the same user to which the data in the channel’s “send data” buffer belonged. 
// Put another way, the Redis Cluster responds to data owned by some user with data also belonging to that same user.
	
// this function has to use the previous pred in some way - how?

	// Pre condition
	// data in connections send data buffer
	some c : Connection | {
		//Check that the receive buffer for that same connection is currently empty
		no State.connection_recv_data[c]
		//Defining some data sitting in the connection's send buffer
		let d1 = State.connection_send_data[c] | {
			//Check there is actually some data in that send buffer
			some d1
			//Grab some more data
			some d2 :  UserData | {
				//Use new helper predicate above
				user_data_for_same_user[d1, d2]
				//Update the buffers
				State.connection_send_data' = State.connection_send_data - (c -> d1)
				State.connection_recv_data' = State.connection_recv_data ++ (c ->d2)
				//Framing and updating last_action
				State.last_action' = RedisProcess
				State.connection_for' = State.connection_for
				State.http_network' = State.http_network
			}
		}
	}
}

// Task 1g: Complete the action_release_connection_and_send_http_response predicate.
pred action_release_connection_and_send_http_response {

	some conn: Connection | {
		// receive data has some
		one State.connection_recv_data[conn]

		some u: User | {
			// fiund the correct users
			(conn -> u) in State.connection_for

			// makes the response
			some resp: HTTPResponse | {
				resp.dest = u
				resp.contents = State.connection_recv_data[conn]

				//check that the network is empty
				no State.http_network				

				//Place this HTTPResponse into the network
				State.http_network' = resp
			}

		//Clear the receive buffer
		State.connection_recv_data' = State.connection_recv_data - (conn -> State.connection_recv_data[conn])
		//Also clear the connection
		State.connection_for' = State.connection_for - (conn -> u)
		//Update last_action
		State.last_action' = ReleaseConnSendResp

		//Framing - unchanged
		State.connection_send_data' = State.connection_send_data	
	}
}
}

// Task 1h: Complete the action_user_request_cancelled predicate.
pred action_user_request_cancelled {

	some conn: Connection, u: User | {
		(conn -> u) in State.connection_for

		State.connection_for' = State.connection_for - (conn -> u)

		some resp: HTTPResponse | {
			resp.dest = u
			resp.contents = DataRequestCancelled

			//check that the network is empty
			no State.http_network				

			//Place this HTTPResponse into the network
			State.http_network' = resp
		}

		// unchanged. 
		State.connection_recv_data' = State.connection_recv_data
		State.connection_send_data' = State.connection_send_data
		State.last_action' = UserReqCancelled

		// this action doesd not check or remove the buffers,
		// basically only clears the connection table, but doesnt fliush the buffer
		// so when another user acquires that connection, then the same connection has some revc data, 
		// which then goes to another user, soon after its validated. 
	}
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
              action_user_send_http_request)
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

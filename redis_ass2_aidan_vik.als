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
fact user_data_disjoint{
	always all disj u1, u2 : User | no (u1.my_data & u2.my_data)
}

//Runs the predicate above with a scope of 3 using exactly 2 users
//Returning predcate is consistent when ran
//run user_data_disjoint for 3 but exactly 2 User

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
       no State.connection_send_data 
	no State.connection_recv_data
	no State.connection_for
	State.last_action = DoNothing
}

// Task 1c: Complete the action_user_send_http_request predicate.
pred action_user_send_http_request {
  // FILL IN HERE

	some u: User, d: UserData | {

		//HTTP network is currently empty
		no State.http_network

		//User must own the data they are sending
		d in u.my_data

		//Find HTTPRequest and assign it to the next http_network
		some req: HTTPRequest | {
			req.contents = d
			req.src = u
			State.http_network' = req
		}
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
	some msg: State.http_network, u: User | {
		msg in HTTPResponse
		msg.dest = u
		
		// assume message content exchange happens
	}

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

	//IFind a HTTP message and connection
	some req: State.http_network, c: Connection | {
		
		//The message is a HTTPRequest
		req in HTTPRequest
		
		// connection has not been allocated
		no State.connection_for[c]

		//remove request from network
		no State.http_network'

		//Allocate the connection and write the data
		State.connection_for' = State.connection_for + (c -> req.src)
		State.connection_send_data' = State.connection_send_data + (c -> req.contents)

		//Update Last Action
		State.last_action' = RecvReqAcquireConn

		//Ensure other states remain unchanged
		State.connection_recv_data' = State.connection_recv_data
	}

}

// Task 1f: Complete user_data_for_same_user and action_redis_process_connection.
pred user_data_for_same_user[d, d2 : UserData] {
  // FILL IN HERE

	//Checks that there is some user that contains both d and d2 in their data
	some u: User | (d + d2) in u.my_data
}

pred action_redis_process_connection {
  // FILL IN HERE

	//For some connection
	some c : Connection | {

		//Check that the receive buffer for that same connection is currently empty
		no State.connection_recv_data[c]

		//Defining some data sitting in the connection's send buffer
		some d1: State.connection_send_data[c], d2: UserData | {

			//Check there is actually some data in that send buffer
			some d1

			//Use new helper predicate above to check d1 d2 part of same user
			user_data_for_same_user[d1, d2]

			//Update the buffers
			State.connection_send_data' = State.connection_send_data - (c -> d1)
			State.connection_recv_data' = State.connection_recv_data + (c ->d2)

			//Framing and updating last_action
			State.last_action' = RedisProcess
			State.connection_for' = State.connection_for
			State.http_network' = State.http_network
		}
	}
}

// Task 1g: Complete the action_release_connection_and_send_http_response predicate.
pred action_release_connection_and_send_http_response {

	//for some connection
	some conn: Connection | {

        // receive data present
        one State.connection_recv_data[conn]

        some u: User | {
            // find the correct user
            (conn -> u) in State.connection_for
            // makes the response
		let d = State.connection_recv_data[conn] | {
			some resp: HTTPResponse | {
			resp.dest = u
			resp.contents = d

			//check that the network is empty
			no State.http_network

			//Place this HTTPResponse into the network
			State.http_network' = resp
			}
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

// for some connection and user
	some conn: Connection, u: User | {
		// user has an existing connection
		(conn -> u) in State.connection_for

		//release connection
		State.connection_for' = State.connection_for - (conn -> u)

		//create response
		some resp: HTTPResponse | {
			resp.dest = u
			resp.contents = DataRequestCancelled

		//check that the network is empty
		no State.http_network

		//Place this HTTPResponse into the network
		State.http_network' = resp
		}

		(no BugFixed implies {
			//Vulnerable Behaviour
			// unchanged. 
			State.connection_recv_data' = State.connection_recv_data
			State.connection_send_data' = State.connection_send_data

		} ) and 
		( some BugFixed implies {
			//Correct Behaviour
			State.connection_recv_data' = State.connection_recv_data - (conn -> UserData)
			State.connection_send_data' = State.connection_send_data - (conn -> UserData)
		} )


		State.last_action' = RequestCancelled

// vulnerable predicate
// this action does not check or remove the buffers,
// basically only clears the connection table, but doesnt flush the buffer
// so when another user acquires that connection, then the same connection has some revc data, 
// which then goes to another user.
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
assert NoDataLeak {
	// for all responses
	always (all r: HTTPResponse | 
		// if its in the network
		r in State.http_network implies 
			// contents designated user is correct or the content is the Request cancelled message
			(r.contents in r.dest.my_data or r.contents = DataRequestCancelled)
	)
}

check NoDataLeak for 4 but 2 User, 1 Connection


// Task 2b: Write your vulnerability run command here, with comments explaining
// the sequence of events and why the vulnerability arises.

// FILL IN HERE
// Task 2b: Vulnerability run command
run vulnerability {

	// 1. User A sends an HTTPRequest.
	action_user_send_http_request ;

	// 2. Frontend acquires Connection 1 for User A.
	action_recv_http_request_and_acquire_connection ;

	// 3. Redis backend processes Connection 1.
	action_redis_process_connection ;

	// 4. User A cancels their request (Buffers fail to clear).
	action_user_request_cancelled ;

	// 5. User A receives the cancellation confirmation.
	action_user_recv_http_response ;

	// 6. User B sends a new HTTPRequest.
	action_user_send_http_request ;

	// 7. Frontend acquires the newly freed Connection 1 for User B.
	action_recv_http_request_and_acquire_connection ;

	// 8. Frontend packages User A's data and sends it to User B.
	action_release_connection_and_send_http_response ;
    
    // Property check evaluates safely at the end of the timeline
	(some r: HTTPResponse | 
		r in State.http_network and 
		r.contents not in r.dest.my_data and 
		r.contents != DataRequestCancelled
	)
} for 4 but 0 BugFixed, exactly 2 User, 10 steps

// =============================================================================
// Task 3: Diagnose the Root Cause
// =============================================================================

// Task 3a: Write your inv predicate and check command here.

// FILL IN HERE
pred inv {
	// for all connections
	all conn: Connection |
			// if it is not acquired
			(no State.connection_for[conn] implies (
				// then it should not have anything in buffers for that connection
				no (State.connection_send_data[conn] + 
				State.connection_recv_data[conn])
			))
}

//Claims that the safe state predicate holds in all reachable states.
assert inv_always_holds {
	always inv
}

// Instructs the solver to try and break the assertion.
check inv_always_holds for 4 but 2 User, 1 Connection

// Task 3b: Write a comment explaining (i) which action predicate causes
// the invariant to be violated and what it fails to do, and (ii) how
// the resulting violation enables the data leakage vulnerability.

// FILL IN HERE

/*
(i) The action_user_request_cancelled predicate is what violates the invariant. When a user cancels
their request, this action correctly removes the mapping within the connection_for table. Although,
it fails to also clear the connection_recv_data & connection_send_data channels, which directly
violated the invariant rule such that unallocated connection must be empty.

(i) When the compromised connection is eventually allocated to a new user through the
action_recv_http_request_and_acquire_connection, the new user obtains the prior user's remaining
data. Finally, when action_release_connection_and_send_http_response is called, it blindly
acquires the leftover data sitting within the receive buffer & loads it into a HTTPResponse which
destination is for the new user, hence completing the cross-user data leak.

*/

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
assert NoDataLeakandInvHolds {
	// if bugfixed is present, both the properties should hold 
	some BugFixed implies (
		always inv
		and

		// Inline logic for NoDataLeak
		(always all msg: State.http_network | msg in HTTPResponse implies (msg.contents in msg.dest.my_data or msg.contents in DataRequestCancelled))
	)
}

check NoDataLeakandInvHolds for 4 but 1 BugFixed, 2 User

// Task 4c(i): Discuss your choice of bounds for the verification checks
// in Task 4b. What behaviours are covered? What confidence does a
// successful check provide? What are the limitations of bounded verification?

// FILL IN HERE
/*
Choice of Bounds: We chose a highly constrained bound. Rather than letting the solver test massive universes, 
we intentionally scoped the check to represent the fundamental architecture of the vulnerability: two competing 
users interacting over a small timeframe. 

Behaviours Covered: This scope exhaustively checks every possible interleaving of actions,
such as sending, acquiring, cancelling, processing, that can occur between two users over 
4 time steps. It perfectly covers the core interaction loop required to trigger a cross-user data leak.

Confidence: A successful check here provides high confidence due to the "Small Scope Hypothesis." As we reasoned during modeling, 
complex system failures usually step down to core interaction issues between a minimum number of entities. 
By definitively proving that the core issue is mathematically solved for 2 users swapping a connection, it is highly probable 
that the logic scales safely to larger deployments.

Limitations: The fundamental limitation of bounded verification is that it is not an absolute mathematical proof for infinite systems. 
If a convoluted vulnerability strictly requires 3 distinct users interacting simultaneously, or requires a sequence of 5 specific 
steps to manifest, this scoped check will miss it and falsely report the system as completely safe.
*/


// Task 4c(ii): Identify at least one simplification or abstraction in this
// model that could mean a real-world vulnerability goes undetected, and
// explain concretely what kind of vulnerability or behaviour it could miss.

// FILL IN HERE

/*
This current model greatly abstracts the concurrecy that occurs in standard networking. As the http_network contains a
lone HTTPMessage, this means the model is limited to having a singular message at any given time travelling within the
http_network. Furthermore, all actions in the model are atomic transitions.

Within the real world, web applications operate in a highly asynchronous manner & servers are multi-threaded as multiple
users are able to send requests simultaneously. As all the actions in this model are atomic, this completely eliminates
the ability to test for concurrency bugs that are common within real-world web servers/networks such as race conditions
or out of order packet deliveries. For example, if an attacker is to flood the network with a large number of DataRequestCancelled
at the exact millisecond a new HTTPRequest is to arrive from another user, it may cause two differing server threads to 
attempt to modify the connection_for table simultaneously, which would lead to state corruption that this model will 
miss entirely.
*/

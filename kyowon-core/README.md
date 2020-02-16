# kyowon-{core,server,client}

# TODO

* [ ] Merge in master and resolve the conflicts, merge back to master.
* [ ] Build examples with reflex to demonstrate the thing
* [ ] Implement and prove Sum type with Liquid Haskell
* [ ] ICFP is Mar 3, 2020

# Stateless behavior

The current model is "stateless" in both the application and the server.

* If the server restarts, it will lose all the messages sent to it.
* If an application restarts, or merely reconnects, it will be sent messages
  sufficient to reconstruct its state.

Specifically, messages follow these rules:

* The client sends messages to the server only once and in-order.
* **Backlog:** When a client connect to the server, the server will send _all_
  previously received messages to that client, regardless of sender, in an
  arbitrary order.
* **Listening:** After a client receives the backlog it will receive a live
  stream of messages in the order they arrive at the server, excluding those
  messages sent by the current client.

# Stateful behavior

Not implemented.

A future model will be stateful, allowing a number of optimizations, but
requiring some changes to how applications function. Since this isn't fully
planned out, I'm leaving it undocumented here. There are notes in the code
about it.

--------------------------
--all the profile stuff
--------------------------
abstract sig Profile {}

sig Group extends Profile {
	
}

sig User extends Profile {
	follows: set Profile,
	friend: set User,
	blocks: set User,
	pDetails: set PersonalDetail
	}

sig PersonalDetail {
	attribute: one PDAttribute
}

sig PDAttribute{}

--facts
fact friendship {all disj u1,u2:User | u2 in u1.friend <=> u1 in u2.friend}
fact friendshipNonReflexiv {no u: User | u in u.friend}
fact blocks{no u:User | u in u.blocks}

--something's wrong with personal Detail...
fact personalDetail {all upds: User.pDetails | no pd:PersonalDetail | pd not in upds}
--fact personalDetail2 {all disj u1,u2: User | no upd:u1.pDetails | upd in u2.pDetails}
fact PDAttribute { all PDs:PersonalDetail.attribute | no PDAs:PDAttribute | PDAs not in PDs}

-----------------------------
--all the Content stuff
-----------------------------
abstract sig Content{
	comments: set Comment,
	isVisibleTo: one Circle
}

sig Text{}

sig Post extends Content{
	text: one Text, --can be empty!
	contains: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{}

----------------
--Messages
----------------
sig Message{
	sender: one User,
	recipient: one User,
	text: one Text, --can be empty!
	contains: set Photo
}

fact message {all m:Message | m.recipient != m.sender}

----------------
--Circle stuff
----------------
sig Circle{}--Contains other users with respect to one user?


-----------------
--commands
-----------------
pred show {
	all u:User | #{u.friend} >1
	}

run show for 5


------------
--checks
------------





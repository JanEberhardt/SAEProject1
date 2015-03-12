--------------------------
--all the profile stuff
--------------------------
abstract sig Profile {}

sig Group extends Profile {
	administrator: some User,
	member: some User	
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
--Each personalDetail must be connected from exactly one user
fact personalDetail {all pd: PersonalDetail | one u: User | pd in u.pDetails}
--Each personalDetail attribute belongs to exactly one personalDetail
fact PDAttribute {all pda: PDAttribute | one pd: PersonalDetail | pda in pd.attribute}
fact administratorIsMember {all g:Group | g.administrator in g.member} 

-----------------------------
--all the Content stuff
-----------------------------
abstract sig Content{
	comments: set Comment,
	isVisibleTo: one Circle,
	owner: one Profile--is basically equal to posted to, right?
}

sig Text{}

sig Post extends Content{
	--text: one Text, --can be empty!
	contains: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{}

--facts

----------------
--Messages
----------------
sig Message{
	sender: one User,
	recipient: one User,
	--text: one Text, --can be empty!
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
	--all u:User | #{u.friend} >1
	#{PersonalDetail} > 1 and #{Post}>3 and #{Photo} > 10 and {all u:User | #{u.friend}>2}
	}

run show for 15


------------
--checks
------------
check personalDetail {all disj u1,u2: User | no upd:u1.pDetails | upd in u2.pDetails}--Two user cannot have the same personal detail




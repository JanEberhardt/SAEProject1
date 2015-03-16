--------------------------
--all the profile stuff
--------------------------
abstract sig Profile {}

sig Group extends Profile {
	administrator: some User,
	member: some User	
}

sig User extends Profile {
	--email: String,
	--name: String,
	follows: set Profile,
	friend: set User,
	blocks: set User,
	pDetails: set PersonalDetail,
	privateCircle: one privateCircle,
	friendsCircle: one friendsCircle,
	friendsOfFriendsCircle: one friendsOfFriendsCircle,
	transitiveFriendsCircle: one transitiveFriendsCircle,
	publicCircle: one publicCircle
	}

sig PersonalDetail {}

--facts
fact friendship {all disj u1,u2:User | u2 in u1.friend <=> u1 in u2.friend}
fact friendshipNonReflexiv {no u: User | u in u.friend}
--User cannot block himself
fact blocks{no u:User | u in u.blocks}
--Each personalDetail must be connected from exactly one user
fact personalDetail {all pd: PersonalDetail | one u: User | pd in u.pDetails}
--Each administrator has to be a member
fact administratorIsMember {all g:Group | g.administrator in g.member}
--There must be at least one administrator
fact oneAdmin {all admin:Group.administrator | #{admin} > 0}
 

-----------------------------
--all the Content stuff
-----------------------------
abstract sig Content{
	comments: set Comment,
	isVisibleTo: one Circle,
	owner: one Profile --is basically equal to posted to, right?
}

sig Post extends Content{
	--text: String, --can be empty
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
	text: String, --can be empty
	contains: set Photo
}

fact message {all m:Message | m.recipient != m.sender}

----------------
--Circle stuff
----------------
abstract sig Circle{
	--users: set User
}--Contains other users with respect to one user?

sig privateCircle extends Circle{
}

sig friendsCircle extends Circle{}

sig friendsOfFriendsCircle extends Circle{}

sig transitiveFriendsCircle extends Circle{}

sig publicCircle extends Circle{}


-----------------
--commands
-----------------
pred show {
	--all u:User | #{u.friend} >1
--	#{Post}>3
	--#{PersonalDetail} > 1 and #{Post}>3 and #{Photo} > 10 and {all u:User | #{u.friend}>2}
	}

run show for 15


------------
--checks
------------
check personalDetail {all disj u1,u2: User | no upd:u1.pDetails | upd in u2.pDetails}--Two user cannot have the same personal detail




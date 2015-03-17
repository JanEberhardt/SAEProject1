open util/integer

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
	pDetails: set PersonalDetail,
	canSee: set Content
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
	circle: one Int,
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

--preds
pred canSee[u: User, c: Content] {
	--u in c.isVisibleTo.users
}

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
fact validCircle {all c: Content | c.circle >= 1 and c.circle <= 5}
-- privacy settings here
fact privateCircles {all c: Content | c.circle = 1 => (all u: User | c in u.canSee <=> u = c.owner)}
fact friendsCircles {all c: Content | c.circle = 2 => (all u: User | c in u.canSee <=> (u in c.owner.friend or u = c.owner))}
fact fofCircles {all c: Content | c.circle = 3 => (all u: User | c in u.canSee <=> (u in c.owner.friend.friend or u in c.owner.friend or u = c.owner))}
fact chainCircles {all c: Content | c.circle = 4 => (all u: User | c in u.canSee <=> (u in c.owner.*friend or u = c.owner))}
fact publicCircles {all c: Content | c.circle = 5 => (all u: User | c in u.canSee)}

-----------------
--commands
-----------------
pred checkCirc3 {
	--all u:User | #{u.friend} >1
	#{c: Content | c.circle != 3} = 0 and #{c: Content | c.circle = 3} >= 2 and
	#{User} = 7  and #{PersonalDetail} = 3 and #{Post} = 5 and #{Photo} = 2 and {all u:User | #{u.friend}=2} and {all u:User | #{u.canSee} >= 1}
}

pred checkCirc5 {
	--all u:User | #{u.friend} >1
	#{c: Content | c.circle != 5} = 0 and #{c: Content | c.circle = 5} >= 2 and
	#{User} = 7  and #{PersonalDetail} = 3 and #{Post} = 5 and #{Photo} = 2 and {all u:User | #{u.friend}=2} and {all u:User | #{u.canSee} >= 1}
}

run checkCirc5 for 15

------------
--checks
------------
check personalDetail {all disj u1,u2: User | no upd:u1.pDetails | upd in u2.pDetails}--Two user cannot have the same personal detail




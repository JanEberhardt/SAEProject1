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

sig PersonalDetail {}


--facts
fact friendship {all disj u1,u2:User | u2 in u1.friend <=> u1 in u2.friend}
fact friendshipNonReflexiv {no u: User | u in u.friend}
fact blocks{no u:User | u in u.blocks}
--Each personalDetail must be connected from exactly one user
fact personalDetail {all pd: PersonalDetail | one u: User | pd in u.pDetails}
fact administratorIsMember {all g:Group | g.administrator in g.member} 
--There must be at least one administrator
fact oneAdmin {all admin:Group.administrator | #{admin} > 0}

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
	contains: set Photo
}

sig Photo extends Content{}

sig Comment extends Content{}

--facts
fact commentCommentsOnOneThing{all com:Comment | {one con:Content | com in con.comments}}
fact commentChainCannotStartWithComment{all com:Comment | one con:(Content-Comment) | com in con.^comments}

--preds
pred canSee[u: User, c: Content] {
	c in u.canSee
}


----------------
--Messages
----------------
sig Message{
	sender: one User,
	recipient: one User,
	contains: set Photo
}

fact message {all m:Message | m.recipient != m.sender}

----------------
--Circle stuff
----------------
fact validCircle {all c: Content | c.circle >= 1 and c.circle <= 5}
-- privacy settings here
--TODO: Where do we check for blocking? Do it here on in canSee Predicate... btw. maybe renaming canSee attribute of User
--since there could be missunderstandings
fact privateCircles {all c: Content | c.circle = 1 => (all u: User | c in u.canSee <=> u = c.owner)}
fact friendsCircles {all c: Content | c.circle = 2 => (all u: User | c in u.canSee <=> (u in c.owner.friend or u = c.owner))}
fact fofCircles {all c: Content | c.circle = 3 => (all u: User | c in u.canSee <=> (u in c.owner.friend.friend or u in c.owner.friend or u = c.owner))}
fact chainCircles {all c: Content | c.circle = 4 => (all u: User | c in u.canSee <=> (u in c.owner.*friend or u = c.owner))}
fact publicCircles {all c: Content | c.circle = 5 => (all u: User | c in u.canSee)}

-----------------
--commands
-----------------
pred checkCirc3 {
	#{c: Content | c.circle != 3} = 0 and #{c: Content | c.circle = 3} >= 2 and
	#{User} = 7  and #{PersonalDetail} = 1 and #{Post} = 5 and #{Photo} = 2 and {all u:User | #{u.friend}=2} and {all u:User | #{u.canSee} >= 1}
}

pred checkCirc5 {
	#{c: Content | c.circle != 5} = 0 and #{c: Content | c.circle = 5} >= 2 and
	#{User} = 7  and #{PersonalDetail} = 3 and #{Post} = 5 and #{Photo} = 2 and {all u:User | #{u.friend}=2} and {all u:User | #{u.canSee} >= 1}
}

run checkCirc3 for 15

pred showSomeComments {
	#{Comment}>3  and #{Comment.comments}>0
}
run showSomeComments for 10


------------
--checks
------------
check pDBelongsToOneUser {all disj u1,u2: User | no upd:u1.pDetails | upd in u2.pDetails}--Two user cannot have the same personal detail
check twoContentsCannotHaveSameComment {all disj c1,c2: Content | no com:c1.comments | com in c2.comments}--Two Contents cannot have the same comment
------------------
--Exercises...
------------------

--Task 3c
pred isOnNewsFeed[u: User, c: Content] {
	{canSee[u,c]} and {c.owner in u.follows}
}
run isOnNewsFeed for 3

-------------
--Task 3d
-------------
--1
check commentChainsAcyclic{all c:Comment | c not in c.^comments}--TODO: I don't need to take reflexif hull here right?

--5
check groupHasMembers{no g:Group | #{g.member}=0}
--6
check allNewsFeedContentIsVisible{all u:User | all c:Content | isOnNewsFeed[u,c] implies canSee[u,c]}

-------------
--Task 3e
-------------
--1
pred showChainOfSizeFive {one c:Comment |  #{c.comments.comments.comments.comments} > 0}
run showChainOfSizeFive for 6

--2
pred threeUsersSevenGroups {#{User}=3 and #{Group}=7 and {all disj g1,g2:Group | g1.member != g2.member}}
run threeUsersSevenGroups for 10

--3
pred fourUsersOneFriendNotTransitiv{#{User}=4 and {all u:User | #{u.friend}>0} }
run fourUsersOneFriendNotTransitiv for 10

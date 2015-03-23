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
	circle: one Int,
	owner: one Profile--is basically equal to posted to, right?
}

abstract sig Commentable extends Content{
	comments: set Comment
}

sig Text{}

sig Post extends Commentable{
	contains: set Photo
}

sig Photo extends Commentable{}

sig Comment extends Commentable{}

sig PersonalDetail extends Content {}

sig Message extends Content{
	recipient: one User,
	contains: set Photo
}

--facts
fact commentCommentsOnOneThing{all com:Comment | {one con:Content | com in con.comments}}
fact commentChainCannotStartWithComment{all com:Comment | one con:(Content-Comment) | com in con.^comments}

--preds
pred canSee[u: User, c: Content] {
	(
	-- circle logic
	((c.circle = 1 => u = c.owner)
	and (c.circle = 2 => (u in c.owner.friend or u = c.owner))
	and (c.circle = 3 => (u in c.owner.friend.friend or u in c.owner.friend or u = c.owner))
	and (c.circle = 4 => (u in c.owner.*friend or u = c.owner)))
	or (c.circle = 5) -- anyone can see public content
	or (u = c.recipient) -- message recipients can always see the message
	) and (not u in c.owner.blocks) -- EXCEPT if the content owner blocked them
}

----------------
--Messages
----------------

fact message {all m:Message | m.recipient != m.owner}

----------------
--Circle stuff
----------------
fact validCircle {all c: Content | c.circle >= 1 and c.circle <= 5}
-- privacy settings here
fact validCanSee {all u: User | all c: Content | c in u.canSee <=> canSee[u, c]}

-----------------
--commands
-----------------
pred checkCirc3 {
	#{c: Content | c.circle != 3} <= 2 and #{c: Content | c.circle = 3} >= 2 and
	#{User} = 7  and #{PersonalDetail} = 1 and #{Post} = 5 and #{Photo} = 2 and {all u:User | #{u.friend}=2} and {all u:User | #{u.canSee} >= 1}
}

pred checkCirc5 {
	#{c: Content | c.circle != 5} <= 2 and #{c: Content | c.circle = 5} >= 2 and
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

--3--TODO
pred fourUsersOneFriendNotTransitiv{#{User}=4 and {all u:User | #{u.friend}>0}} --and {one u1,u2:User | u1 != u2 and u1 not in u2.^friend } 
run fourUsersOneFriendNotTransitiv for 10

--4 is against the privacy stuff, right?
--TODO

--5
pred photoWithPhotoNotByPoster{ #{Post} = 1 and #{Post.contains}=1 and {all p:Photo | p.circle != 5} }
run photoWithPhotoNotByPoster for 3

--6
pred friendOfFriendPostWithPhoto{#{Post} = 1 and {all p:Post | p.circle = 3}}
run friendOfFriendPostWithPhoto for 5

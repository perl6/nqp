#! nqp

# check comments

say('1..4');

#Comment preceding
say("ok 1");

say("ok 2"); #Comment following

#say("not ok 3");
#          say("not ok 4");

{ say('ok 3'); } # comment
{ say('ok 4'); }

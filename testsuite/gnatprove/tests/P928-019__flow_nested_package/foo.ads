procedure Foo (Secret : Integer;
               Y      : out Integer)
with Global  => null,
     Depends => (Y    => null,
                 null => Secret),
     Post    => Y = Secret;

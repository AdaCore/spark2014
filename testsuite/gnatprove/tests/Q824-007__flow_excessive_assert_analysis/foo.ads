package Foo is

  type Level_0 is record
     A1 : Boolean;
     A2 : Boolean;
     A3 : Boolean;
     A4 : Boolean;
     A5 : Boolean;
  end record;

  type Level_1 is record
     B1 : Level_0;
     B2 : Level_0;
     B3 : Level_0;
     B4 : Level_0;
  end record;

  type Level_2 is record
     C1 : Level_1;
     C2 : Level_1;
     C3 : Level_1;
  end record;

  Red   : Level_2;
  Black : Level_2;

  procedure Initialise (X : Integer)
  with Global => (Output => (Red, Black)),
       Pre    => X > 1;

end Foo;

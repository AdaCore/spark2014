package Simple_OO_Without_Contracts is pragma Elaborate_Body;
   G1, G2, G3, G4 : Integer := 0;

   type T is tagged record
      X : Integer;
   end record;

   procedure Do_Stuff (Par : T);

   type T1 is new T with record
      Y : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T1);

   type T2 is new T1 with record
      Z1 : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T2);

   type T3 is new T1 with record
      Z2 : Integer;
   end record;

   overriding
   procedure Do_Stuff (Par : T3);
end Simple_OO_Without_Contracts;

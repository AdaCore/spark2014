package T is

   type Stupid_Record is record
      A : Integer;
      B : Boolean;
      C : Float;
   end record;

   type Stupid_Array is array (Integer range <>) of Stupid_Record;

   type Foo is new Stupid_Array (0 .. Stupid_Record'Size / 8)
      with Annotate => (GNATprove, False_Positive, "o<", "ow");
   --pragma Annotate (GNATprove, False_Positive, "o<", "ow");

   Dummy : constant Foo := (others => (0, True, 1.0));

end T;

package Violations is

   function Increment_And_Add (X, Y : in out Integer) return Integer;

   procedure Operate;

   type Ptr is access Integer;

   procedure Operate (Data1, Data2, Data3 : Ptr);

   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive);

end Violations;

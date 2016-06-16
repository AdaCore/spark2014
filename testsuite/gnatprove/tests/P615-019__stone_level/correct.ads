package Correct is

   --  from violations.ads

   procedure Increment_And_Add (X, Y : in out Integer; Result : out Integer);

   procedure Operate;

   package Ptr_Accesses is
      type Ptr is private;
      function Get (X : Ptr) return Integer;
      procedure Set (X : Ptr; V : Integer);
   private
      pragma SPARK_Mode (Off);
      type Ptr is access Integer;
   end Ptr_Accesses;

   procedure Operate (Data1, Data2, Data3 : Ptr_Accesses.Ptr);

   function Find_Before_Delim (S : String; C, Delim : Character) return Positive;
   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive);

   --  from all_violations.ads

   procedure Increment (Result : out Integer);

   procedure Log (X : Integer)
     with Global => null;

   function Increment_And_Log (X : Integer) return Integer;

end Correct;

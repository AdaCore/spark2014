package body Correct is

   --  from violations.adb

   procedure Increment_And_Add (X, Y : in out Integer; Result : out Integer) is
   begin
      X := X + 1;
      Y := Y + 1;
      Result := X + Y;
   end Increment_And_Add;

   Data1 : Integer;
   Data2 : Boolean;

   package Memory_Accesses is
      procedure Write_Data3 (V : Integer);
   end Memory_Accesses;

   package body Memory_Accesses
     with SPARK_Mode => Off
   is
      Data3 : access Integer;

      procedure Write_Data3 (V : Integer) is
      begin
         Data3.all := 42;
      end Write_Data3;
   end Memory_Accesses;

   procedure Operate is
   begin
      Data1 := 42;
      Data2 := False;
      Memory_Accesses.Write_Data3 (42);
   end Operate;

   package body Ptr_Accesses
     with SPARK_Mode => Off
   is
      function Get (X : Ptr) return Integer is (X.all);
      procedure Set (X : Ptr; V : Integer) is
      begin
         X.all := V;
      end Set;
   end Ptr_Accesses;

   procedure Operate (Data1, Data2, Data3 : Ptr_Accesses.Ptr) is
      use Ptr_Accesses;
   begin
      Set (Data1, Get (Data2));
      Set (Data2, Get (Data2) + Get (Data3));
      Set (Data3, 42);
   end Operate;

   Not_Found : exception;

   function Find_Before_Delim (S : String; C, Delim : Character) return Positive is
   begin
      for J in S'Range loop
         if S(J) = Delim then
            raise Not_Found;
         elsif S(J) = C then
            return J;
         end if;
      end loop;
      raise Not_Found;
   end Find_Before_Delim;

   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive)
     with SPARK_Mode => Off
   is
   begin
      Position := Find_Before_Delim (S, C, Delim);
      Found := True;
   exception
      when Not_Found =>
         Position := 1;
         Found := False;
   end Find_Before_Delim;

   --  from all_violations.adb

   Count : Integer := 0;

   procedure Increment (Result : out Integer) is
   begin
      Count := Count + 1;
      Result := Count;
   end Increment;

   Last : Integer := 0;

   procedure Log (X : Integer)
     with SPARK_Mode => Off
   is
   begin
      Last := X;
   end Log;

   function Increment_And_Log (X : Integer) return Integer is
   begin
      Log (X);
      return X + 1;
   end Increment_And_Log;

end Correct;

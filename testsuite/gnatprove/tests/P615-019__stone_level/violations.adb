package body Violations is

   function Increment_And_Add (X, Y : in out Integer) return Integer is
   begin
      X := X + 1;
      Y := Y + 1;
      return X + Y;
   end Increment_And_Add;

   Data1 : Integer;
   Data2 : Boolean;
   Data3 : access Integer;

   procedure Operate is
   begin
      Data1 := 42;
      Data2 := False;
      Data3.all := 42;
   end Operate;

   procedure Operate (Data1, Data2, Data3 : Ptr) is
   begin
      Data1.all := Data2.all;
      Data2.all := Data2.all + Data3.all;
      Data3.all := 42;
   end Operate;

   Not_Found : exception;

   procedure Find_Before_Delim
     (S        : String;
      C, Delim : Character;
      Found    : out Boolean;
      Position : out Positive)
   is
   begin
      for J in S'Range loop
         if S(J) = Delim then
            raise Not_Found;
         elsif S(J) = C then
            Position := J;
            Found := True;
            return;
         end if;
      end loop;
      raise Not_Found;
   exception
      when Not_Found =>
         Position := 1;
         Found := False;
   end Find_Before_Delim;

end Violations;

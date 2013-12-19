package body P
  with SPARK_Mode => On
is
   procedure Op1 (A : in out Integer)
   is
      -- A is "in out" so a variable not a constant, therefore...
      subtype LS4 is Integer range A .. 10;   -- illegal
   begin
      A := A + 2;

      --  The range constraint of a loop parameter specification
      --  may contain variables, so
      for I in Integer range 1 .. A loop -- legal
         A := A + 1;
      end loop;

   end Op1;


   procedure Op2 (A : in     String;
                  L :    out Natural)
   is
      AF : constant Positive := A'First;
      AL : constant Positive := A'Last;

      -- Constraints on subtypes where constraint depends
      -- on "in" unconstrained array parameter. Should all
      -- be OK since "in" param is a constant
      subtype AI1 is Positive range AF .. AL; -- legal

      subtype AI2 is Positive range AF .. A'Last; -- legal
      subtype AI3 is Positive range A'First .. AL; -- legal
      subtype AI4 is Positive range A'First .. A'Last; -- legal
      subtype AI5 is Positive range A'Range; -- legal

      T : Natural := 0;
   begin
      for I in Positive range A'Range loop -- legal
         T := T + Character'Pos (A (I));
      end loop;
      L := T;
   end Op2;



   procedure Op3 (A : in out String;
                  L :    out Natural)
   is
      AF : constant Positive := A'First;
      AL : constant Positive := A'Last;

      -- Constraints on subtypes where constraint depends
      -- on "in out" unconstrained array parameter
      subtype AI1 is Positive range AF .. AL; -- legal

      subtype AI2 is Positive range AF .. A'Last; -- legal
      subtype AI3 is Positive range A'First .. AL; -- legal
      subtype AI4 is Positive range A'First .. A'Last; -- legal
      subtype AI5 is Positive range A'Range; -- legal

      T : Natural := 0;
   begin
      for I in Positive range A'Range loop -- legal
         T := T + Character'Pos (A (I));
         A (I) := Character'Succ (A (I));
      end loop;
      L := T;
   end Op3;

   function Same_Length (S : String) return String is
      Result : String (S'Range) := (others => ' '); -- legal
   begin
      for I in Positive range Result'Range loop -- legal
         Result (I) := Character'Succ (S (I));
      end loop;
      return Result;
   end Same_Length;

end P;

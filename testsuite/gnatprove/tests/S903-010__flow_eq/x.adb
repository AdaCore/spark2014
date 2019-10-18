procedure X is
   type Y is new Natural;
--   type New_Bool is new Boolean;
   type New_Bool is (My_True, My_False);

   function "abs" (Left : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "abs");

   function "and" (Left, Right : New_Bool) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "and");

   function "mod" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "mod");

   function "not" (Left : New_Bool) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "not");

   function "or" (Left, Right : New_Bool) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "or");

   function "rem" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "rem");

   function "xor" (Left, Right : New_Bool) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "xor");

   function "=" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "=");

   function "<" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "<");

   function "<=" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, "<=");

   function ">" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, ">");

   function ">=" (Left, Right : Y) return Boolean with Pre => True;
   pragma Annotate (GNATprove, Terminating, ">=");

   function "+" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "+");

   function "-" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "-");

   function "&" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "&");

   function "*" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "*");

   function "/" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "/");

   function "**" (Left, Right : Y) return Integer with Pre => True;
   pragma Annotate (GNATprove, Terminating, "**");

   function "=" (Left, Right : Y) return Boolean is
   begin
      while True loop
         null;
      end loop;
      return Integer (Left) = Integer (Right);
   end;

   function "<" (Left, Right : Y) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Integer (Left) < Integer (Right);
   end;

   function "<=" (Left, Right : Y) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Integer (Left) <= Integer (Right);
   end;

   function ">" (Left, Right : Y) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Integer (Left) > Integer (Right);
   end;

   function ">=" (Left, Right : Y) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Integer (Left) >= Integer (Right);
   end;

   function "abs" (Left : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left);
   end;

   function "and" (Left, Right : New_Bool) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Left = Right;
   end;

   function "mod" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer (Right);
   end;

   function "not" (Left : New_Bool) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Left = My_False;
   end;

   function "or" (Left, Right : New_Bool) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Left = Right;
   end;

   function "rem" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "xor" (Left, Right : New_Bool) return Boolean is
   begin
       while True loop
          null;
       end loop;
       return Left = Right;
   end;

   function "+" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "-" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "&" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "*" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "/" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   function "**" (Left, Right : Y) return Integer is
   begin
       while True loop
          null;
       end loop;
       return Integer(Left) + Integer(Right);
   end;

   A, B : Y := 0;
   C, D : New_Bool := My_True;
begin
   pragma Assert (A = B);
   pragma Assert (A /= B);
   pragma Assert (A < B);
   pragma Assert (A <= B);
   pragma Assert (A > B);
   pragma Assert (A >= B);
   pragma Assert (abs (A) = Integer (0));
   pragma Assert (C and C);
   pragma Assert (A mod B = Integer (0));
   pragma Assert (not C);
   pragma Assert (C or D);
   pragma Assert (A rem B = Integer (0));
   pragma Assert (C xor D);
   pragma Assert (A + B = Integer (0));
   pragma Assert (A - B = Integer (0));
   pragma Assert (A & B = Integer (0));
   pragma Assert (A * B = Integer (0));
   pragma Assert (A / B = Integer (0));
   pragma Assert (A ** B = Integer (0));
end;

procedure Do_Checks is

   Zero : Integer := 0;
   Branch : Natural := 105;

   --  Check that a range check is performed on every subtype indication with
   --  a range_constraint.
   procedure Do_Range_Check is
   begin
      case Branch is
         --  subtype_indication in a subtype_declaration
         when 0 =>
            declare
               subtype S is Positive range Zero .. 1;  --  BAD
            begin
               null;
            end;
         when 1 =>
            declare
               subtype S is Positive range Zero .. Zero - 1;  --  OK
            begin
               null;
            end;

         --  subtype_indication in an object_declaration
         when 2 =>
            declare
               A : Positive range Zero .. 1;  --  BAD
               pragma Unreferenced (A);
            begin
               null;
            end;
         when 3 =>
            declare
               A : Positive range Zero .. Zero - 1;  --  OK
               pragma Unreferenced (A);
            begin
               null;
            end;

         --  subtype_indication in a derived_type_definition
         when 4 =>
            declare
               type S is new Positive range Zero .. 1;  --  BAD
            begin
               null;
            end;
         when 5 =>
            declare
               type S is new Positive range Zero .. Zero - 1;  --  OK
            begin
               null;
            end;

         --  subtype_indication in a constrained_array_definition
         when 6 =>
            declare
               type S is array (Positive range Zero .. 1) of Integer;  --  BAD
            begin
               null;
            end;
         when 7 =>
            declare
               type S is array (Positive range Zero .. Zero - 1) of Positive;  --  OK
            begin
               null;
            end;

         --  subtype_indication in a loop_parameter_specification
         when 8 =>
            for J in Positive range Zero .. 1 loop  --  BAD
               null;
            end loop;
         when 9 =>
            for J in Positive range Zero .. Zero - 1 loop  --  OK
               null;
            end loop;

         --  subtype_indication in a component_definition
         when 10 =>
            declare
               type S is record
                  C : Positive range Zero .. 1;  --  BAD
               end record;
            begin
               null;
            end;
         when 11 =>
            declare
               type S is record
                  C : Positive range Zero .. Zero - 1;  --  OK
               end record;
            begin
               null;
            end;

         --  subtype_indication in an index_constraint
         when 12 =>
            declare
               subtype S is String (Positive range Zero .. 1);  --  BAD
            begin
               null;
            end;
         when 13 =>
            declare
               subtype S is String (Positive range Zero .. Zero - 1);  --  OK
            begin
               null;
            end;

         --  subtype_indication in a slice
         --  UNCOMMENT AFTER M919-016 HAS BEEN CORRECTED
         --  when 14 =>
         --     declare
         --        A : String := "hello world";
         --        B : String := A(Positive range Zero .. 1);  --  BAD
         --     begin
         --        null;
         --     end;
         --  when 15 =>
         --     declare
         --        A : String := "hello world";
         --        B : String := A(Positive range Zero .. Zero - 1);  --  OK
         --     begin
         --        null;
         --     end;

         --  subtype_indication in a variant
         when 16 =>
            declare
               type S (B : Boolean) is record
                  case B is
                     when True =>
                        C : Positive range Zero .. 1;  --  BAD
                     when False =>
                        null;
                  end case;
               end record;
            begin
               null;
            end;
         when 17 =>
            declare
               type S (B : Boolean) is record
                  case B is
                     when True =>
                        C : Positive range Zero .. Zero - 1;  --  OK
                     when False =>
                        null;
                  end case;
               end record;
            begin
               null;
            end;

         --  subtype_indication in an array_component_association
         when 18 =>
            declare
               A : String(1 .. 10) := (Positive range Zero .. 1 => '0');  --  BAD
            begin
               null;
            end;
         when 19 =>
            declare
               A : String(1 .. 0) := (Positive range Zero .. Zero - 1 => '0');  --  OK
            begin
               null;
            end;

         --  subtype_indication in case_expression or case_statement is always static

         --  subtype_indication in an iterator_specification
         --  UNCOMMENT WHEN SUPPORTED IN GNATPROVE
         --  when 20 =>
         --     declare
         --        A : String := "hello world";
         --     begin
         --        for J : Positive range Zero .. 1 of A loop  --  BAD
         --           null;
         --        end loop;
         --     end;
         --  when 21 =>
         --     declare
         --        A : String(1 .. 0);
         --     begin
         --        for J : Positive range Zero .. Zero - 1 of A loop  --  OK
         --           null;
         --        end loop;
         --     end;

         --  subtype_indication in extended_return_statement is always static

         when others =>
            null;
      end case;
   end Do_Range_Check;

   --  Check that a length check is performed where needed
   procedure Do_Length_Check is
      type A1 is array (Natural range <>) of Boolean;
      subtype A2 is A1(0 .. 10);
   begin
      case Branch is
         --  logical operator on array
         --  UNCOMMENT WHEN SUPPORTED IN GNATPROVE
         --  when 100 =>
         --     declare
         --        procedure P (X, Y : in out A1) is
         --        begin
         --           X := X and Y;  --  BAD
         --        end;
         --        X : A1(0 .. 10) := (others => False);
         --        Y : A1(1 .. 10) := (others => False);
         --     begin
         --        P (X, Y);
         --     end;
         --  when 101 =>
         --     declare
         --        procedure P (X, Y : in out A1) is
         --        begin
         --           X := X and Y;  --  OK
         --        end;
         --        X : A1(0 .. 10) := (others => False);
         --        Y : A1(1 .. 11) := (others => False);
         --     begin
         --        P (X, Y);
         --     end;

         --  value conversion to constrained array
         when 102 =>
            declare
               procedure P (X : A1; Y : out A2) is
               begin
                  Y := X;  --  BAD
               end;
               X : A1(1 .. 10) := (others => False);
               Y : A2;
            begin
               P (X, Y);
            end;
         when 103 =>
            declare
               procedure P (X : A1; Y : out A2) with
                 Pre => X'First = 1 and X'Last = 11
               is
               begin
                  Y := X;  --  OK
               end;
               X : A1(1 .. 11) := (others => False);
               Y : A2;
            begin
               P (X, Y);
            end;

         --  view conversion to constrained array
         when 104 =>
            declare
               procedure P1 (X : in out A2) is
               begin
                  null;
               end;
               procedure P2 (X : in out A1) is
               begin
                  P1(X);  --  BAD
               end;
               X : A1(1 .. 10) := (others => False);
            begin
               P2 (X);
            end;
         when 105 =>
            declare
               procedure P1 (X : in out A2) is
               begin
                  null;
               end;
               procedure P2 (X : in out A1) with
                 Pre => X'First = 1 and X'Last = 11
               is
               begin
                  P1(X);  --  OK
               end;
               X : A1(1 .. 11) := (others => False);
            begin
               P2 (X);
            end;

         when others =>
            null;
      end case;
   end Do_Length_Check;

begin
   Do_Length_Check;
   Do_Range_Check;
end Do_Checks;

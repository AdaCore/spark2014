pragma Unevaluated_Use_Of_Old (Allow);

package Basics is

   type Rec (Disc : Boolean := False) is record
      case Disc is
         when True =>
            A : Integer;
         when False =>
            B : Integer;
      end case;
   end record;

   type Index is range 1 .. 10;
   type Table is array (Index range <>) of Integer;

   procedure Swap (X, Y : in out Integer)
   with Post => X = Y'Old and Y = X'Old;

   The_Rec : Rec;
   The_Table : Table (1 .. 10);

   function Value_Rec (R : Rec) return Integer is
     (if R.Disc then R.A else R.B);

   procedure Bump_Rec (R : in out Rec)
     with Pre => Value_Rec (R) < Integer'Last,
          Post => Value_Rec (R) = Value_Rec (R)'Old + 1;

   procedure Swap_Table (T : in out Table; I, J : Index)
     with
       Pre => I in T'Range and J in T'Range,
     Post => (declare
                     Val_I : constant Integer := T (I)'Old;
                       Val_J : constant Integer := T (J)'Old;
                     begin
                       T = (T'Old with delta I => Val_J, J => Val_I));

   procedure Bump_The_Rec
     with Pre => Value_Rec (The_Rec) < Integer'Last,
          Post => Value_Rec (The_Rec) = Value_Rec (The_Rec)'Old + 1;

   procedure Swap_The_Table (I, J : Index)
     with Post => (declare
                     Val_I : constant Integer := The_Table (I)'Old;
                       Val_J : constant Integer := The_Table (J)'Old;
                     begin
                       The_Table = (The_Table'Old with delta I => Val_J, J => Val_I));

   procedure Init_Rec (R : out Rec)
   with Post => Value_Rec (R) = 1;

   procedure Init_Table (T : out Table)
     with Pre => T'Length > 0,
     Post => T =
       (for X in T'Range =>
         (if X = T'Last then 2
          elsif X = T'First then 1
          else 0));

   procedure Init_The_Rec
   with Post => Value_Rec (The_Rec) = 1;

   procedure Init_The_Table;

end Basics;

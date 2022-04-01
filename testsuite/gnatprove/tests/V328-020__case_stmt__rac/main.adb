with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

  --  Int

  type Index is range 1 .. 20;

  subtype Tenths is Index range 10 .. 20;

  subtype Ten_Fourteen is Tenths range 10 .. 14;

  subtype Fifteen_Twenty is Tenths
    with Static_Predicate => Fifteen_Twenty in 15 .. 20;

  subtype Lower_Than_Five is Index
    with Static_Predicate => Lower_Than_Five in 1 .. 4;

  subtype Five_To_Nine is Index
    with Static_Predicate => (Five_To_Nine not in Lower_Than_Five) and
                             not (Five_To_Nine in Tenths);

  --  Days

  type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

  subtype Weekend is Day
    with Static_Predicate => Weekend in Sat | Sun;

  subtype Wednesday is Day range Mon .. Sun
    with Static_Predicate => Wednesday in Wed .. Wed;

  --  Functions

  function Index_Range (I : Index) return String;
  --  Case statement with Index range in choice expression

  function Index_Subtype (K : Index) return String;
  --  Subtype (range and static predicate) in choice expression

  function Week_Range (D : Day) return String;
  --  Case statement with enum range in choice expression

  function Week_Static_Predicate (D : Day) return String;
  --  Subtype with static predicate in choice expr

  --  Implementations

  ---------------
  -- Int_Range --
  ---------------

  function Index_Range (I : Index) return String is
  begin
    case I is
      when 10 .. 18 => return "Work";
      when 19 .. 20 => return "Party";
      when others   => return "Sleep";
    end case;
  end Index_Range;

  -----------------
  -- Int_Subtype --
  -----------------

  function Index_Subtype (K : Index) return String is
  begin
    case K is
      when Ten_Fourteen    => return "10 - 14";
      when Fifteen_Twenty  => return "15 - 20";
      when Lower_Than_Five => return "1 - 4";
      when Five_To_Nine    => return "5 - 9";
    end case;
  end Index_Subtype;

  ----------------
  -- Week_Range --
  ----------------

  function Week_Range (D : Day) return String is
  begin
    case D is
      when Mon .. Thu => return "Work";
      when Fri        => return "Party";
      when Sat .. Sun => return "Sleep";
    end case;
  end Week_Range;

  ---------------------------
  -- Week_Static_Predicate --
  ---------------------------

  function Week_Static_Predicate (D : Day) return String is
  begin
    case D is
      when Weekend   => return "Sleep";
      when Wednesday => return "Nothing";
      when others    => return "Work";
    end case;
  end Week_Static_Predicate;

begin

  Put_Line ("Index_Range");
  Put_Line ("Expect Work: "  & Index_Range (11));
  Put_Line ("Expect Party: " & Index_Range (20));
  Put_Line ("Expect Sleep: " & Index_Range (5));
  Put_Line ("");

  Put_Line ("Index_Subtype");
  Put_Line ("11 is betwen "  & Index_Subtype (11));
  Put_Line ("20 is between " & Index_Subtype (20));
  Put_Line ("5 is between "  & Index_Subtype (5));
  Put_Line ("");

  Put_Line ("Week_Range");
  Put_Line ("Expect Work: "  & Week_Range (Tue));
  Put_Line ("Expect Party: " & Week_Range (Fri));
  Put_Line ("Expect Sleep: " & Week_Range (Sat));
  Put_Line ("");

  Put_Line ("Week_Static_Predicate");
  Put_Line ("Expect Sleep: "   & Week_Static_Predicate (Sun));
  Put_Line ("Expect Nothing: " & Week_Static_Predicate (Wed));
  Put_Line ("Expect Work: "    & Week_Static_Predicate (Thu));

end Main;

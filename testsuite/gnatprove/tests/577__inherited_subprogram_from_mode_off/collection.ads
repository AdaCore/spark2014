package Collection with SPARK_Mode is
   pragma Elaborate_Body; --  Freezing screams without it...

   package Root_Pack is
      type Root is tagged null record;
      procedure P (X : Root) is null;
      procedure Q (I : Integer; X : Root) is null;
      function F (X : Root) return Integer is (0);
      function G (X : Root) return Integer is (1);
      function Create return Root is (null record);
   end Root_Pack;
   use Root_Pack;

   package In_Private is
      type Child is new Root with private;
      Witness : constant Child;
   private
      type Missing_Link is new Root with null record;
      procedure P (X : Missing_Link) is null;
      function F (X : Missing_Link) return Integer is (2);
      function Create return Missing_Link;
      type Child is new Missing_Link with null record;
      Witness : constant Child := (null record);
   end In_Private;

   package Bad_Descendants_Off is
      type Bad_Descendant is new Root with private;
      --  Private intermediate type define primitives

      type Other_Bad_Descendant is new In_Private.Child with private;
      --  Private intermediate type (in nested package) define primitives

      type Good_Descendant is new In_Private.Child with private;
      procedure P (X : Good_Descendant);
      function F (X : Good_Descendant) return Integer;
      function Create return Good_Descendant;
      --  No issue.

      type Bad_Over_Good is new Good_Descendant with private;
      function G (X : Bad_Over_Good) return Integer is (36);
      function Create return Bad_Over_Good;
      --  Private intermediate type (after Good_Descendant) defines
      --  primitives.

      type Cascading_Bad_Descendant is new Other_Bad_Descendant with private;
      procedure Q (I : Integer; X : Cascading_Bad_Descendant) is null;
      --  No extra errors, all the bad subprograms are already reported for
      --  Other_Bad_Descendant

      type Bad_Controlling is new Root with private;
      --  No intermediate derivation, but controlling result function should
      --  still be overriden.

   private
      pragma SPARK_Mode (Off);
      type Child is new Root with null record;
      procedure P (X : Child) is null;
      function G (X : Child) return Integer is (3);
      type Bad_Descendant is new Child with null record;

      type Other_Child is new In_Private.Child with null record;
      function F (X : Other_Child) return Integer is (4);
      function Create return Other_Child is (In_Private.Witness with null record);
      subtype Other_Child_Sub is Other_Child with Predicate => True;
      package Nested is
         type Other_Something is new Other_Child_Sub with private;
      private
         type Other_Grand_Child is new Other_Child_Sub with null record;
         procedure Q (I : Integer; X : Other_Grand_Child) is null;
         type Other_Something is new Other_Grand_Child with null record;
      end Nested;
      type Other_Bad_Descendant is new Nested.Other_Something with null record;

      type Nice_Child is new In_Private.Child with null record;
      procedure P (X : Nice_Child) is null;
      function F (X : Nice_Child) return Integer is (5);
      type Good_Descendant is new Nice_Child with null record;

      type Not_Good_Anymore is new Good_Descendant with null record;
      procedure Q (I : Integer; X : Not_Good_Anymore) is null;
      type Bad_Over_Good is new Not_Good_Anymore with null record;

      type Somewhat_Ok_Intermediate is new Other_Bad_Descendant with null record;
      procedure Q (I : Integer; X : Somewhat_Ok_Intermediate) is null;
      type Cascading_Bad_Descendant is new Somewhat_Ok_Intermediate with null record;

      type Bad_Controlling is new Root with null record;
   end Bad_Descendants_Off;

   --  Version with Hide instead of SPARK_Mode

   package Bad_Descendants_Hide is
      type Bad_Descendant is new Root with private;
      --  Private intermediate type define primitives

      type Other_Bad_Descendant is new In_Private.Child with private;
      --  Private intermediate type (in nested package) define primitives

      type Good_Descendant is new In_Private.Child with private;
      procedure P (X : Good_Descendant);
      function F (X : Good_Descendant) return Integer;
      function Create return Good_Descendant;
      --  No issue.

      type Bad_Over_Good is new Good_Descendant with private;
      function G (X : Bad_Over_Good) return Integer is (36);
      function Create return Bad_Over_Good;
      --  Private intermediate type (after Good_Descendant) defines
      --  primitives.

      type Cascading_Bad_Descendant is new Other_Bad_Descendant with private;
      procedure Q (I : Integer; X : Cascading_Bad_Descendant) is null;
      --  No extra errors, all the bad subprograms are already reported for
      --  Other_Bad_Descendant

      type Bad_Controlling is new Root with private;
      --  No intermediate derivation, but controlling result function should
      --  still be overriden.

   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part", Bad_Descendants_Hide);
      type Child is new Root with null record;
      procedure P (X : Child) is null;
      function G (X : Child) return Integer is (3);
      type Bad_Descendant is new Child with null record;

      type Other_Child is new In_Private.Child with null record;
      function F (X : Other_Child) return Integer is (4);
      function Create return Other_Child is (In_private.Witness with null record);
      subtype Other_Child_Sub is Other_Child with Predicate => True;
      package Nested is
         type Other_Something is new Other_Child_Sub with private;
      private
         type Other_Grand_Child is new Other_Child_Sub with null record;
         procedure Q (I : Integer; X : Other_Grand_Child) is null;
         type Other_Something is new Other_Grand_Child with null record;
      end Nested;
      type Other_Bad_Descendant is new Nested.Other_Something with null record;

      type Nice_Child is new In_Private.Child with null record;
      procedure P (X : Nice_Child) is null;
      function F (X : Nice_Child) return Integer is (5);
      type Good_Descendant is new Nice_Child with null record;

      type Not_Good_Anymore is new Good_Descendant with null record;
      procedure Q (I : Integer; X : Not_Good_Anymore) is null;
      type Bad_Over_Good is new Not_Good_Anymore with null record;

      type Somewhat_Ok_Intermediate is new Other_Bad_Descendant with null record;
      procedure Q (I : Integer; X : Somewhat_Ok_Intermediate) is null;
      type Cascading_Bad_Descendant is new Somewhat_Ok_Intermediate with null record;

      type Bad_Controlling is new Root with null record;
   end Bad_Descendants_Hide;

end Collection;

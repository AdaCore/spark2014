package Unclear with SPARK_Mode is

    package Root is
      type Root is tagged null record;
      procedure P (X : Root) is null with Pre'Class => False, Post'Class => True;
   end Root;

   package Other is
      type Root is tagged null record;
      type Child is new Root with null record;
      procedure P (X : Child) is null with Pre'Class => False, Post'Class => True;
   end Other;

   package KO_1 is
      type T is private;
      procedure P (X : T) with Post => False;
   private
      type T is new Root.Root with null record;
      procedure P (X : T) is null;
   end KO_1;

   package KO_2 is
      type T is private;
      procedure P (X : T) with Contract_Cases => (False => False);
   private
      type T is new Root.Root with null record;
      procedure P (X : T) is null;
   end KO_2;

   package KO_3 is
      type T is private;
      procedure P (X : T);
   private
      type T is new Root.Root with null record;
      procedure P (X : T) is null;
   end KO_3;

   package KO_4 is
      type T is tagged private;
      procedure P (X : T) is null;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type T is new Root.Root with null record;
   end KO_4;

   package KO_5 is
      type T is tagged private;
      procedure P (X : T) is null with Post'Class => False;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type T is new Root.Root with null record;
   end KO_5;

   package KO_6 is
      type T is new Other.Root with private;
      procedure P (X : T) is null;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type T is new Other.Child with null record;
   end KO_6;

   package KO_7 is
      type T is new Other.Child with private;
      procedure P (X : T) is null;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type GrandChild is new Other.Child with null record;
      procedure P (X : GrandChild) is null with Pre'Class => True;
      type T is new GrandChild with null record;
   end KO_7;

   package OK_1 is
      type T is private;
      procedure P (X : T) with Pre => False, Post => False;
   private
      type T is new Root.Root with null record;
      procedure P (X : T) is null;
   end OK_1;

   package OK_2 is
      type T is private;
      procedure P (X : T) with Pre => False, Contract_Cases => (False => False);
   private
      type T is new Root.Root with null record;
      procedure P (X : T) is null;
   end OK_2;

   package OK_3 is
      type T is private;
      procedure Q (X : T);
   private
      type T is new Root.Root with null record;
      procedure Q (X : T) is null;
   end OK_3;

   package OK_4 is
      type T is tagged private;
      procedure P (X : T) is null with Pre'Class => True;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type T is new Root.Root with null record;
   end OK_4;

   package OK_5 is
      type T is tagged private;
      procedure P (X : T) is null;
   private
      type T is new Root.Root with null record;
   end OK_5;

   package OK_6 is
      type T is new Other.Child with private;
      procedure P (X : T) is null;
   private
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      type GrandChild is new Other.Child with null record;
      type T is new GrandChild with null record;
   end OK_6;

end Unclear;

package Illegal_Hide_Private with
   SPARK_Mode
is

   --  Generic units occuring inside package with hidden private parts. They
   --  cannot be instantiated outside of the package.

   generic
   package Nested is
      procedure P;
   end Nested;

   generic
   procedure Proc;

   --  Type with duplicated predicates with different visibilities

   type T_Preds (F, L : Natural) is private with
     Predicate => F <= L;

   --  Entirely relaxed type

   type T_Relaxed is private;

   --  Type with ownership

   type T_Ownership is private;

   --  Type whose predefined equality is restricted

   type T_Restricted_Eq is private;

   --  Annotation shall have 3 parameters

   function Bad_Ent return Boolean is (True);
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Bad_Ent);

   --  Annotation at the wrong place

   package Nested_No_Priv is
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      function F return Boolean is (True);
   end Nested_No_Priv;

   package Nested_Too_Late is
      function F return Boolean;
   private
      function F return Boolean is (True);
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
   end Nested_Too_Late;

   --  Unhide annotation

   package Nested_Unhide is
      function F return Boolean;
   private
      pragma Annotate (GNATprove, Unhide_Info, "Private_Part");
      function F return Boolean is (True);
   end Nested_Unhide;

private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type T_Preds (F, L : Natural) is record
      V : Natural;
   end record with
     Dynamic_Predicate => F <= V and V <= L;

   type Int_Relaxed is new Integer with Relaxed_Initialization;

   type T_Relaxed is record
      F : Int_Relaxed;
   end record;

   type Int_Acc is access Integer;

   type Holder is record
      C : Int_Acc;
   end record;

   function "=" (X, Y : Holder) return Boolean is
     (if X.C = null then Y.C = null
      else Y.C /= null and then X.C.all = Y.C.all);

   type T_Ownership is record
      F : Holder;
   end record;

   type T_Restricted_Eq is access constant Integer;

   --  Hidden function, it should not be visible in user code

   function F_Hidden return Boolean is (True);

   --  Hidden package, the annotation is illegal

   package P_Nested is
      function F return Boolean;
   private
      pragma Inspection_Point;
      pragma Annotate (GNATprove, Hide_Info, "Private_Part");
      function F return Boolean is (True);
   end P_Nested;

end Illegal_Hide_Private;

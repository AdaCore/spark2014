
--  Covers code checking placement of various annotation pragma.

package Pragma_Placement with SPARK_Mode is
   
   --  Pragma Annotate are not allowed to follow generics. Using a package
   --  wrapper containing the pragma is fine.

   generic
      type T (<>) is private;
   function Identity (X : T) return T;
   pragma Annotate (GNATprove, Skip_Proof, Identity);
   function Identity (X : T) return T is (X);

   generic
      type T (<>) is private;
   package Foo_P is
      function Bar (X : T) return T is (X);
   end Foo_P;
   pragma Annotate (GNATprove, Skip_Proof, Foo_P);
   
   generic
      type T (<>) is private;
   package Wrapper is
      pragma Annotate (GNATprove, Skip_Proof, Wrapper);
      function Wrapped (X : T) return T is (X);
   end Wrapper;
   package Wrapper_Instance is new Wrapper (T => Integer);

   generic
      N : Integer;
   function Overflowing (X : Integer) return Integer
     with Global => null, Post => Overflowing'Result = X + N;
   function Overflowing (X : Integer) return Integer is (X + N);
   function Overflowing_Instance is new Overflowing (N => 42);
   pragma Annotate (GNATprove, Skip_Proof, Overflowing_Instance);

   --  Placement of annotation pragma after a type full view
   
   type T is mod 128;
   type U is mod 256;
   pragma Annotate (GNATprove, No_Wrap_Around, U); -- OK, immediately after.
   pragma Annotate (GNATprove, No_Wrap_Around, T); -- KO, Too late.

   --  Placement of annotation pragma after a type private view,
   --  & placement of annotation pragma Ownership.
   
   package Owned_Types is
      type A is private;
      type B is private;
      pragma Annotate (GNATprove, Ownership, "needs_reclamation", B); -- OK
      pragma Annotate (GNATprove, Ownership, "needs_reclamation", A); -- KO
      
      type C is private;
      pragma Annotate (GNATprove, Ownership, "needs_reclamation", C);

      function Is_Reclaimed_B (X : B) return Boolean is (True);
      function Is_Reclaimed_C (X : C) return Boolean is (True);
      pragma Annotate (GNATprove, Ownership, "is_reclaimed", Is_Reclaimed_B); -- KO
      pragma Annotate (GNATprove, Ownership, "is_reclaimed", Is_Reclaimed_C); -- OK

   private
      pragma SPARK_Mode (Off);
      type A is new Integer;
      type B is new Integer;
      type C is new Integer;
   end Owned_Types;

   --  Placement of annotation pragma At_End_Borrow

   function AEB_1 (X : access constant Integer) return access constant Integer
   is (X)
     with Ghost;
   function AEB_2 (X : access constant Integer) return access constant Integer
   is (X)
     with Ghost;
   pragma Annotate (GNATprove, At_End_Borrow, AEB_2); -- OK
   pragma Annotate (GNATprove, At_End_Borrow, AEB_1); -- KO
  
   --  Placement of annotation pragma Automatic_Instantiation.
   
   function F91 (X : Integer) return Integer;
   procedure F91_Low (X : Integer)
     with
       Global => null,
       Ghost,
       Pre => X <= 101,
       Post => F91 (X) = 91;
   procedure F91_High (X : Integer)
     with
       Global => null,
       Ghost,
       Pre => X > 100,
       Post => F91 (X) = X - 10;
   pragma Annotate (GNATprove, Automatic_Instantiation, F91_High); -- OK
   pragma Annotate (GNATprove, Automatic_Instantiation, F91_Low); -- KO

   --  Placement of annotation pragma Higher_Order_Specialization.

   function Specialized_1
     (X : Integer;
      F : access function (X : Integer) return Integer) return Integer
       with Post => Specialized_1'Result = F (X);
   function Specialized_2
     (X : Integer;
      F : access function (X : Integer) return Integer) return Integer
       with Post => Specialized_2'Result = F (F (X));
   pragma Annotate (GNATprove, Higher_Order_Specialization, Specialized_2); -- OK
   pragma Annotate (GNATprove, Higher_Order_Specialization, Specialized_1); -- KO

   --  Placement of annotation pragma Inline_For_Proof

   function Identity_Again (X : Integer) return Integer is (X);
   function Another_Identity (X : Integer) return Integer is (X);
   pragma Annotate (GNATprove, Inline_For_Proof, Another_Identity); -- OK
   pragma Annotate (GNATprove, Inline_For_Proof, Identity_Again); -- KO

   --  Placement of annotation pragma Logical_Equal
   
   function Strictest_Equal (X, Y : Integer) return Boolean is (X = Y);
   function Just_As_Strict_Equal (X, Y : Integer) return Boolean is (X = Y);
   pragma Annotate (GNATprove, Logical_Equal, Strictest_Equal); -- KO
   pragma Annotate (GNATprove, Logical_Equal, Just_As_Strict_Equal); -- OK
   
end Pragma_Placement;
pragma Annotate (GNATprove, Skip_Proof, Pragma_Placement);

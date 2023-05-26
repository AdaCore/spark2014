procedure Main with SPARK_Mode is

   --  Test that the tag is updated on return statements

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
      type Child is new Root with record
         G : Integer;
      end record;
   end Nested;
   use Nested;

   function Copy (X : Root) return Root is (X) with
     Post => (X in Root) = (Copy'Result in Root);  -- @POSTCONDITION:FAIL

   function Copy2 (X : Root) return Root with
     Post => (X in Root) = (Copy2'Result in Root);  -- @POSTCONDITION:FAIL

   function Copy2 (X : Root) return Root is
   begin
      return X;
   end Copy2;

   function Copy3 (X : Root) return Root with
     Post => (X in Root) = (Copy3'Result in Root);  -- @POSTCONDITION:FAIL

   function Copy3 (X : Root) return Root is
      Y : constant Root := X;
   begin
      return Y;
   end Copy3;

   --  Test compatibility with inline annotations

   function Copy4 (X : Root) return Root with
     Post => Copy4'Result = X,
     Annotate => (GNATprove, Inline_For_Proof);  -- @INLINE_ANNOTATION:PASS

   function Copy4 (X : Root) return Root is
   begin
      return X;
   end Copy4;

   function Copy5 (X : Root) return Root with
     Post => Copy5'Result = X,
     Annotate => (GNATprove, Inline_For_Proof);  -- @INLINE_ANNOTATION:PASS

   function Copy5 (X : Root) return Root is
      Y : constant Root := X;
   begin
      return Y;
   end Copy5;

   C : Child := (others => 1);
   R : Root := Copy (Root (C));
begin
   null;
end Main;

pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Test_Callback_Bad with SPARK_Mode is
   type Incr_Fun is not null access function
     (X : Integer) return Integer
   with Pre => X < 100,
     Post => Incr_Fun'Result >= X;
   type P_Fun is access protected function
     (X : Integer) return Integer;

   type Borrow is access function (X : access Integer) return access Integer;

   protected P is
      function Get return Integer;
   private
      X : Integer := 0;
   end P;

   type Root is tagged record
      X : Integer;
   end record;

   procedure Prim (X : Root);

   procedure Test;

   package Nested with SPARK_Mode => Off is
      type T is access all Integer;
   end Nested;
   use all type Nested.T;

   type Incr_Bad is not null access function
     (X : Nested.T) return Integer;

   type Incr_Bad2 is not null access function
     (X : Nested.T; Y : Integer) return Integer
   with Pre => Y < 100,
     Post => Incr_Bad2'Result >= Y;

   type With_Inv is private;

   type Incr_Inv is not null access function
     (X : With_Inv) return Integer;
   type Incr_Inv_2 is not null access function
     (X : Integer) return With_Inv;
private
   type With_Inv is new Integer with
     Type_Invariant => Integer (With_Inv) in Natural;
end Test_Callback_Bad;

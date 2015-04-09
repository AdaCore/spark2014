with Private_With_Attributes; use Private_With_Attributes;

package Public_Derives_Private with SPARK_Mode is
   type Grand_Child_Private_Tagged is new Child_Private_Tagged with record
      F2 : Natural := 0;
   end record;
   type Grand_Grand_Child_Private_Tagged is new Grand_Child_Private_Tagged with record
      F3 : Natural := 0;
   end record;
   type Grand_Child is new Child with record
      F2 : Natural := 0;
   end record;
   type Child_Discr is new Root_Discr with record
      F1 : Natural := 0;
   end record;

   type Private_Grand_Child_Private_Tagged is private;

   function Get_F2 (G : Private_Grand_Child_Private_Tagged) return Natural;

private
   type Private_Grand_Child_Private_Tagged is new Child_Private_Tagged with record
      F2 : Natural := 0;
   end record;

   function Get_F2 (G : Private_Grand_Child_Private_Tagged) return Natural
   is (G.F2);

end Public_Derives_Private;

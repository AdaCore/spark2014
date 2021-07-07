with Ext; use Ext;
package Bad_Inheritance with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;

   function Get (X : Root) return Integer is (X.F);

   type Inter is interface;

   function Get (X : Inter) return Integer is abstract;

   type Child is new Root and Inter with record
      G : Integer;
   end record;

   function Get (X : Child) return Integer is (X.G);

   type Child2 is new Root and Inter with record
      G : Integer;
   end record;

   type Grand_Child2 is new Child2 with record
      H : Integer;
   end record;

   function Get (X : Grand_Child2) return Integer is (X.H);

   type Bad is abstract new Root and Mode_Off.Bad_Inter with record
      G : Integer;
   end record;

   X : Ext.Untagged;
   I : Integer := Ext.Get (X);
end Bad_Inheritance;

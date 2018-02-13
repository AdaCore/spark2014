with Q;

package P with SPARK_Mode is
   type T is array (Boolean) of Integer
     with Default_Component_Value => Q.C;
   --                                ^^^
   --  Ada RM 3.6.(22.2/3) says: "This aspect shall be specified by a static
   --  expression, and that expression shall be explicit, even if the aspect
   --  has a boolean type." However, static expressions might be not in SPARK
   --  if they reference static constants declared within the scope of a
   --  SPARK_Mode => Off annotation. This is what happens here.
end;

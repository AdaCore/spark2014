with DIC_Pred; use DIC_Pred;
with Containers;
package Use_Dic_Pred with SPARK_Mode is
   X : T;
   V : Containers.Container (10);

   subtype scont is Containers.Container (8);

   type Container3 is new Containers.Container (7);

   type Container4 is new scont;

   type Container2 is private with Default_Initial_Condition => True;
private
   type Container2 is new Containers.Container (9);
end Use_DIC_Pred;

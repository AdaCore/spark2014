with My_Container_Model;
with My_Container_Contains;
with My_Container;
procedure Test_Containers with SPARK_Mode is
   C1 : My_Container.Container;
   P1 : My_Container.Cursor;
   C2 : My_Container_Contains.Container;
   P2 : Natural;
   C3 : My_Container_Model.Container;
   P3 : Natural;
begin
   My_Container.Modify (C1);
   pragma Assume (My_Container.Has_Element (C1, P1));
   pragma Assert (My_Container.Valid (My_Container.Element (C1, P1)));
   My_Container_Contains.Modify (C2);
   pragma Assume (My_Container_Contains.Mem (C2, P2));
   pragma Assert (My_Container_Contains.Valid (P2));
   My_Container_Model.Modify (C3);
   pragma Assume (My_Container_Model.M_Has_Element
                  (My_Container_Model.Get_Model (C3), P3));
   pragma Assert (My_Container_Model.Valid
                  (My_Container_Model.M_Element
                     (My_Container_Model.Get_Model (C3), P3)));
end Test_Containers;

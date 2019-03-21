pragma SPARK_Mode;
with Linked_List_Types_Types; use Linked_List_Types_Types;
-- Remove all nodes with given key value from source list and
-- prepend them to target list
--
procedure Update_Lists_Inlined (Source, Target : in out List; Key : Character);

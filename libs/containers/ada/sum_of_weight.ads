with Ada.Containers.Doubly_Linked_Lists;

generic
   with package DLL is new Ada.Containers.Doubly_Linked_Lists (<>);
   with function Weight (E : DLL.Element_Type) return Integer;
function Sum_Of_Weight (L : DLL.List) return Integer;

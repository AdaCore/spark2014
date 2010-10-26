with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Sets;
with Sum_Of_Weight;

package Common is

   type Monitoring is record
      Failed : Boolean;
      Active : Boolean;
   end record;

   function Detects_Failure (E : Monitoring) return Boolean;

   function Is_Active (E : Monitoring) return Boolean;

   function Activate (E : Monitoring) return Monitoring;

   function Weight (E : Monitoring) return Integer;

   package DLL is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Monitoring);

   function Num_Of_Active is new Sum_Of_Weight (DLL, Weight);

   type Recovery is record
      Priority : Natural;
   end record;

   function "<" (Left, Right : Recovery) return Boolean;

   package OS is new Ada.Containers.Ordered_Sets
     (Element_Type => Recovery);

end Common;

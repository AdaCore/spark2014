generic


package Generic_Parent.Child_Instance is

   type Object is new Generic_Parent.Object with private;

   overriding
   function Create return Object with Inline;

   overriding
   procedure Print( This: in out Object );

private
   type Object is new Generic_Parent.Object with
       record
           B: Element;
       end record;

   overriding
   procedure Increment( This: in out Object );

   overriding
   function Create return Object
   is (Object'(Generic_Parent.Create with
               B => Element'Last));

end Generic_Parent.Child_Instance;

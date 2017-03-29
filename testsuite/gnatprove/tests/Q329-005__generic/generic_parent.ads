generic
   type Element is range <>;

package Generic_Parent is

   type Object is tagged private;

   function Create return Object with Inline;

   procedure Print( This: in out Object );

private
   type Object is tagged
       record
           A: Element;
       end record;

   procedure Increment( This: in out Object );

   function Create return Object
   is (Object'(A => Element'First));

end Generic_Parent;

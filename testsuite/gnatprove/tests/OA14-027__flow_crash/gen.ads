generic
   type T is (<>);
package Gen
is

private
   type P is record
      F1 : T;
      F2 : T;
   end record;

   C : constant P := (F1 => T'First, F2 => T'First);
end Gen;

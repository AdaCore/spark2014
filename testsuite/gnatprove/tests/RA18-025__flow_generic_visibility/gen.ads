generic
package Gen is
   procedure Dummy;
   --  Only needed to force completion with a body, which in turn provides
   --  a context where we can instantiate a generic *private* child package.

   type T is private;
private
   type T is record
      C : Integer := 0;
   end record;
   --  This full type declaration is visible in the public part of a *private*
   --  child.
end;

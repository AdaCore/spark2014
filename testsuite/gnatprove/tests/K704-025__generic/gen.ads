
generic
   type T is private;
package Gen is
   function Echo (X : T) return T is (X);
end Gen;

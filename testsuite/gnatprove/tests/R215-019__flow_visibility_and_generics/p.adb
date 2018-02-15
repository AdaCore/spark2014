with Gen;
package body P
  with Refined_State => (Hash => Instance.State)
is
   package Instance is new Gen;
end P;

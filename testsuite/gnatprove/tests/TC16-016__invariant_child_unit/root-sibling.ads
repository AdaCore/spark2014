with Root.Child; use Root.Child;
with Root.Child.Grand_Child; use Root.Child.Grand_Child;
package Root.Sibling with SPARK_Mode is
   function OK1 return Child_T; --@INVARIANT_CHECK:NONE
   function OK1 return Grand_Child_T; --@INVARIANT_CHECK:NONE
private
   function OK1 return Child_T is (OK);
   function OK1 return Grand_Child_T is (OK);
end Root.Sibling;

with Interfaces.C;
package Nonsparkpkg with SPARK_Mode => Off is
    type uint32_t is new Interfaces.C.unsigned;
    type int32_t is new Interfaces.C.int;
end Nonsparkpkg;

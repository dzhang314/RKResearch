module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart003

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e450 : o1.mul b86 b35=b971 := by decide
theorem e451 : o1.mul b86 b36=b1000 := by decide
theorem e452 : o1.mul b86 b37=b1001 := by decide
theorem e453 : o1.mul b86 b38=b974 := by decide
theorem e454 : o1.mul b86 b39=b1002 := by decide
theorem e455 : o1.mul b86 b40=b1003 := by decide
theorem e456 : o1.scale b86 b998=b1013 := @scale_cons V1 _ o1 b86 b40 b1003 (List.nil : V2) (List.nil : V2) b1013 e455 e26 (by rfl)
theorem e457 : o1.scale b86 b996=b1012 := @scale_cons V1 _ o1 b86 b39 b1002 b998 b1013 b1012 e454 e456 (by rfl)
theorem e458 : o1.scale b86 b994=b1011 := @scale_cons V1 _ o1 b86 b38 b974 b996 b1012 b1011 e453 e457 (by rfl)
theorem e459 : o1.scale b86 b992=b1010 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b994 b1011 b1010 e19 e458 (by rfl)
theorem e460 : o1.scale b86 b990=b1009 := @scale_cons V1 _ o1 b86 b37 b1001 b992 b1010 b1009 e452 e459 (by rfl)
theorem e461 : o1.scale b86 b988=b1008 := @scale_cons V1 _ o1 b86 b36 b1000 b990 b1009 b1008 e451 e460 (by rfl)
theorem e462 : o1.scale b86 b986=b1007 := @scale_cons V1 _ o1 b86 b35 b971 b988 b1008 b1007 e450 e461 (by rfl)
theorem e463 : o1.scale b86 b984=b1006 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b986 b1007 b1006 e19 e462 (by rfl)
theorem e464 : o1.scale b86 b982=b1005 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b984 b1006 b1005 e19 e463 (by rfl)
theorem e465 : o1.scale b86 b41=b1004 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b982 b1005 b1004 e19 e464 (by rfl)
theorem e466 : o1.add b971 (List.nil : V1)=b971 := by rfl
theorem e467 : o1.add b1000 b977=b972 := by decide
theorem e468 : o1.add b1001 b978=b967 := by decide
theorem e469 : o1.add (List.nil : V1) b973=b973 := by rfl
theorem e470 : o1.add b974 (List.nil : V1)=b974 := by rfl
theorem e471 : o1.add b1002 b979=b975 := by decide
theorem e472 : o1.add b1003 b980=b563 := by decide
theorem e473 : o2.add (List.nil : V2) b999=b999 := by rfl
theorem e474 : o2.add b1013 b997=b1023 := @add_cons V1 _ o1 b1003 b980 b563 (List.nil : V2) b999 b999 b1023 e472 e473 (by rfl)
theorem e475 : o2.add b1012 b995=b1022 := @add_cons V1 _ o1 b1002 b979 b975 b1013 b997 b1023 b1022 e471 e474 (by rfl)
theorem e476 : o2.add b1011 b993=b1021 := @add_cons V1 _ o1 b974 (List.nil : V1) b974 b1012 b995 b1022 b1021 e470 e475 (by rfl)
theorem e477 : o2.add b1010 b991=b1020 := @add_cons V1 _ o1 (List.nil : V1) b973 b973 b1011 b993 b1021 b1020 e469 e476 (by rfl)
theorem e478 : o2.add b1009 b989=b1019 := @add_cons V1 _ o1 b1001 b978 b967 b1010 b991 b1020 b1019 e468 e477 (by rfl)
theorem e479 : o2.add b1008 b987=b1018 := @add_cons V1 _ o1 b1000 b977 b972 b1009 b989 b1019 b1018 e467 e478 (by rfl)
theorem e480 : o2.add b1007 b985=b1017 := @add_cons V1 _ o1 b971 (List.nil : V1) b971 b1008 b987 b1018 b1017 e466 e479 (by rfl)
theorem e481 : o2.add b1006 b983=b1016 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1007 b985 b1017 b1016 e34 e480 (by rfl)
theorem e482 : o2.add b1005 b981=b1015 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1006 b983 b1016 b1015 e34 e481 (by rfl)
theorem e483 : o2.add b1004 b1014=b976 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1005 b981 b1015 b976 e34 e482 (by rfl)
theorem e484 : o2.mul b603 b41=b976 := @mul_cons V1 _ o1 b86 b610 b41 b981 b1004 b1014 b976 e449 e465 (by rfl) e483
theorem e485 : o1.mul b85 b35=b965 := by decide
theorem e486 : o1.mul b85 b36=b1024 := by decide
theorem e487 : o1.mul b85 b37=b1025 := by decide
theorem e488 : o1.mul b85 b38=b1026 := by decide
theorem e489 : o1.mul b85 b39=b1027 := by decide
theorem e490 : o1.mul b85 b40=b1028 := by decide
theorem e491 : o1.scale b85 b998=b1038 := @scale_cons V1 _ o1 b85 b40 b1028 (List.nil : V2) (List.nil : V2) b1038 e490 e57 (by rfl)
theorem e492 : o1.scale b85 b996=b1037 := @scale_cons V1 _ o1 b85 b39 b1027 b998 b1038 b1037 e489 e491 (by rfl)
theorem e493 : o1.scale b85 b994=b1036 := @scale_cons V1 _ o1 b85 b38 b1026 b996 b1037 b1036 e488 e492 (by rfl)
theorem e494 : o1.scale b85 b992=b1035 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b994 b1036 b1035 e50 e493 (by rfl)
theorem e495 : o1.scale b85 b990=b1034 := @scale_cons V1 _ o1 b85 b37 b1025 b992 b1035 b1034 e487 e494 (by rfl)
theorem e496 : o1.scale b85 b988=b1033 := @scale_cons V1 _ o1 b85 b36 b1024 b990 b1034 b1033 e486 e495 (by rfl)
theorem e497 : o1.scale b85 b986=b1032 := @scale_cons V1 _ o1 b85 b35 b965 b988 b1033 b1032 e485 e496 (by rfl)
theorem e498 : o1.scale b85 b984=b1031 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b986 b1032 b1031 e50 e497 (by rfl)
theorem e499 : o1.scale b85 b982=b1030 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b984 b1031 b1030 e50 e498 (by rfl)
theorem e500 : o1.scale b85 b41=b1029 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b982 b1030 b1029 e50 e499 (by rfl)
theorem e501 : o1.add b965 (List.nil : V1)=b965 := by rfl
theorem e502 : o1.add b1024 b971=b966 := by decide
theorem e503 : o1.add b1025 b972=b961 := by decide
theorem e504 : o1.add (List.nil : V1) b967=b967 := by rfl
theorem e505 : o1.add b1026 b973=b968 := by decide
theorem e506 : o1.add b1027 b974=b969 := by decide
theorem e507 : o1.add b1028 b975=b562 := by decide
theorem e508 : o2.add (List.nil : V2) b1023=b1023 := by rfl
theorem e509 : o2.add b1038 b1022=b1048 := @add_cons V1 _ o1 b1028 b975 b562 (List.nil : V2) b1023 b1023 b1048 e507 e508 (by rfl)
theorem e510 : o2.add b1037 b1021=b1047 := @add_cons V1 _ o1 b1027 b974 b969 b1038 b1022 b1048 b1047 e506 e509 (by rfl)
theorem e511 : o2.add b1036 b1020=b1046 := @add_cons V1 _ o1 b1026 b973 b968 b1037 b1021 b1047 b1046 e505 e510 (by rfl)
theorem e512 : o2.add b1035 b1019=b1045 := @add_cons V1 _ o1 (List.nil : V1) b967 b967 b1036 b1020 b1046 b1045 e504 e511 (by rfl)
theorem e513 : o2.add b1034 b1018=b1044 := @add_cons V1 _ o1 b1025 b972 b961 b1035 b1019 b1045 b1044 e503 e512 (by rfl)
theorem e514 : o2.add b1033 b1017=b1043 := @add_cons V1 _ o1 b1024 b971 b966 b1034 b1018 b1044 b1043 e502 e513 (by rfl)
theorem e515 : o2.add b1032 b1016=b1042 := @add_cons V1 _ o1 b965 (List.nil : V1) b965 b1033 b1017 b1043 b1042 e501 e514 (by rfl)
theorem e516 : o2.add b1031 b1015=b1041 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1032 b1016 b1042 b1041 e34 e515 (by rfl)
theorem e517 : o2.add b1030 b976=b1040 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1031 b1015 b1041 b1040 e34 e516 (by rfl)
theorem e518 : o2.add b1029 b1039=b970 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1030 b976 b1040 b970 e34 e517 (by rfl)
theorem e519 : o2.mul b596 b41=b970 := @mul_cons V1 _ o1 b85 b603 b41 b976 b1029 b1039 b970 e484 e500 (by rfl) e518
theorem e520 : o1.mul b84 b35=b959 := by decide
theorem e521 : o1.mul b84 b36=b1049 := by decide
theorem e522 : o1.mul b84 b37=b1050 := by decide
theorem e523 : o1.mul b84 b38=b1051 := by decide
theorem e524 : o1.mul b84 b39=b1052 := by decide
theorem e525 : o1.mul b84 b40=b1053 := by decide
theorem e526 : o1.scale b84 b998=b1063 := @scale_cons V1 _ o1 b84 b40 b1053 (List.nil : V2) (List.nil : V2) b1063 e525 e87 (by rfl)
theorem e527 : o1.scale b84 b996=b1062 := @scale_cons V1 _ o1 b84 b39 b1052 b998 b1063 b1062 e524 e526 (by rfl)
theorem e528 : o1.scale b84 b994=b1061 := @scale_cons V1 _ o1 b84 b38 b1051 b996 b1062 b1061 e523 e527 (by rfl)
theorem e529 : o1.scale b84 b992=b1060 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b994 b1061 b1060 e80 e528 (by rfl)
theorem e530 : o1.scale b84 b990=b1059 := @scale_cons V1 _ o1 b84 b37 b1050 b992 b1060 b1059 e522 e529 (by rfl)
theorem e531 : o1.scale b84 b988=b1058 := @scale_cons V1 _ o1 b84 b36 b1049 b990 b1059 b1058 e521 e530 (by rfl)
theorem e532 : o1.scale b84 b986=b1057 := @scale_cons V1 _ o1 b84 b35 b959 b988 b1058 b1057 e520 e531 (by rfl)
theorem e533 : o1.scale b84 b984=b1056 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b986 b1057 b1056 e80 e532 (by rfl)
theorem e534 : o1.scale b84 b982=b1055 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b984 b1056 b1055 e80 e533 (by rfl)
theorem e535 : o1.scale b84 b41=b1054 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b982 b1055 b1054 e80 e534 (by rfl)
theorem e536 : o1.add b959 (List.nil : V1)=b959 := by rfl
theorem e537 : o1.add b1049 b965=b960 := by decide
theorem e538 : o1.add b1050 b966=b557 := by decide
theorem e539 : o1.add (List.nil : V1) b961=b961 := by rfl
theorem e540 : o1.add b1051 b967=b962 := by decide
theorem e541 : o1.add b1052 b968=b963 := by decide
theorem e542 : o1.add b1053 b969=b561 := by decide
theorem e543 : o2.add (List.nil : V2) b1048=b1048 := by rfl
theorem e544 : o2.add b1063 b1047=b1073 := @add_cons V1 _ o1 b1053 b969 b561 (List.nil : V2) b1048 b1048 b1073 e542 e543 (by rfl)
theorem e545 : o2.add b1062 b1046=b1072 := @add_cons V1 _ o1 b1052 b968 b963 b1063 b1047 b1073 b1072 e541 e544 (by rfl)
theorem e546 : o2.add b1061 b1045=b1071 := @add_cons V1 _ o1 b1051 b967 b962 b1062 b1046 b1072 b1071 e540 e545 (by rfl)
theorem e547 : o2.add b1060 b1044=b1070 := @add_cons V1 _ o1 (List.nil : V1) b961 b961 b1061 b1045 b1071 b1070 e539 e546 (by rfl)
theorem e548 : o2.add b1059 b1043=b1069 := @add_cons V1 _ o1 b1050 b966 b557 b1060 b1044 b1070 b1069 e538 e547 (by rfl)
theorem e549 : o2.add b1058 b1042=b1068 := @add_cons V1 _ o1 b1049 b965 b960 b1059 b1043 b1069 b1068 e537 e548 (by rfl)
theorem e550 : o2.add b1057 b1041=b1067 := @add_cons V1 _ o1 b959 (List.nil : V1) b959 b1058 b1042 b1068 b1067 e536 e549 (by rfl)
theorem e551 : o2.add b1056 b1040=b1066 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1057 b1041 b1067 b1066 e34 e550 (by rfl)
theorem e552 : o2.add b1055 b970=b1065 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1056 b1040 b1066 b1065 e34 e551 (by rfl)
theorem e553 : o2.add b1054 b1064=b964 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1055 b970 b1065 b964 e34 e552 (by rfl)
theorem e554 : o2.mul b589 b41=b964 := @mul_cons V1 _ o1 b84 b596 b41 b970 b1054 b1064 b964 e519 e535 (by rfl) e553
theorem e555 : o1.mul b83 b35=b402 := by decide
theorem e556 : o1.mul b83 b36=b1074 := by decide
theorem e557 : o1.mul b83 b37=b1075 := by decide
theorem e558 : o1.mul b83 b38=b1076 := by decide
theorem e559 : o1.mul b83 b39=b1077 := by decide
theorem e560 : o1.mul b83 b40=b1078 := by decide
theorem e561 : o1.scale b83 b998=b1088 := @scale_cons V1 _ o1 b83 b40 b1078 (List.nil : V2) (List.nil : V2) b1088 e560 e117 (by rfl)
theorem e562 : o1.scale b83 b996=b1087 := @scale_cons V1 _ o1 b83 b39 b1077 b998 b1088 b1087 e559 e561 (by rfl)
theorem e563 : o1.scale b83 b994=b1086 := @scale_cons V1 _ o1 b83 b38 b1076 b996 b1087 b1086 e558 e562 (by rfl)
theorem e564 : o1.scale b83 b992=b1085 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b994 b1086 b1085 e110 e563 (by rfl)
theorem e565 : o1.scale b83 b990=b1084 := @scale_cons V1 _ o1 b83 b37 b1075 b992 b1085 b1084 e557 e564 (by rfl)
theorem e566 : o1.scale b83 b988=b1083 := @scale_cons V1 _ o1 b83 b36 b1074 b990 b1084 b1083 e556 e565 (by rfl)
theorem e567 : o1.scale b83 b986=b1082 := @scale_cons V1 _ o1 b83 b35 b402 b988 b1083 b1082 e555 e566 (by rfl)
theorem e568 : o1.scale b83 b984=b1081 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b986 b1082 b1081 e110 e567 (by rfl)
theorem e569 : o1.scale b83 b982=b1080 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b984 b1081 b1080 e110 e568 (by rfl)
theorem e570 : o1.scale b83 b41=b1079 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b982 b1080 b1079 e110 e569 (by rfl)
theorem e571 : o1.add b402 (List.nil : V1)=b402 := by rfl
theorem e572 : o1.add b1074 b959=b555 := by decide
theorem e573 : o1.add b1075 b960=b556 := by decide
theorem e574 : o1.add (List.nil : V1) b557=b557 := by rfl
theorem e575 : o1.add b1076 b961=b558 := by decide
theorem e576 : o1.add b1077 b962=b559 := by decide
theorem e577 : o1.add b1078 b963=b560 := by decide
theorem e578 : o2.add (List.nil : V2) b1073=b1073 := by rfl
theorem e579 : o2.add b1088 b1072=b1098 := @add_cons V1 _ o1 b1078 b963 b560 (List.nil : V2) b1073 b1073 b1098 e577 e578 (by rfl)
theorem e580 : o2.add b1087 b1071=b1097 := @add_cons V1 _ o1 b1077 b962 b559 b1088 b1072 b1098 b1097 e576 e579 (by rfl)
theorem e581 : o2.add b1086 b1070=b1096 := @add_cons V1 _ o1 b1076 b961 b558 b1087 b1071 b1097 b1096 e575 e580 (by rfl)
theorem e582 : o2.add b1085 b1069=b1095 := @add_cons V1 _ o1 (List.nil : V1) b557 b557 b1086 b1070 b1096 b1095 e574 e581 (by rfl)
theorem e583 : o2.add b1084 b1068=b1094 := @add_cons V1 _ o1 b1075 b960 b556 b1085 b1069 b1095 b1094 e573 e582 (by rfl)
theorem e584 : o2.add b1083 b1067=b1093 := @add_cons V1 _ o1 b1074 b959 b555 b1084 b1068 b1094 b1093 e572 e583 (by rfl)
theorem e585 : o2.add b1082 b1066=b1092 := @add_cons V1 _ o1 b402 (List.nil : V1) b402 b1083 b1067 b1093 b1092 e571 e584 (by rfl)
theorem e586 : o2.add b1081 b1065=b1091 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1082 b1066 b1092 b1091 e34 e585 (by rfl)
theorem e587 : o2.add b1080 b964=b1090 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1081 b1065 b1091 b1090 e34 e586 (by rfl)
theorem e588 : o2.add b1079 b1089=b565 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1080 b964 b1090 b565 e34 e587 (by rfl)
theorem e589 : o2.mul b88 b41=b565 := @mul_cons V1 _ o1 b83 b589 b41 b964 b1079 b1089 b565 e554 e570 (by rfl) e588
theorem e590 : o2.mul (List.nil : V2) b47=(List.nil : V2) := by rfl
theorem e591 : o1.mul b87 b42=b1116 := by decide
theorem e592 : o1.mul b87 b43=b1117 := by decide
theorem e593 : o1.mul b87 b44=b1113 := by decide
theorem e594 : o1.mul b87 b45=b1118 := by decide
theorem e595 : o1.mul b87 b46=b575 := by decide
theorem e596 : o1.scale b87 b1138=b1139 := @scale_cons V1 _ o1 b87 b46 b575 (List.nil : V2) (List.nil : V2) b1139 e595 e9 (by rfl)
theorem e597 : o1.scale b87 b1136=b1137 := @scale_cons V1 _ o1 b87 b45 b1118 b1138 b1139 b1137 e594 e596 (by rfl)
theorem e598 : o1.scale b87 b1134=b1135 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1136 b1137 b1135 e2 e597 (by rfl)
theorem e599 : o1.scale b87 b1132=b1133 := @scale_cons V1 _ o1 b87 b44 b1113 b1134 b1135 b1133 e593 e598 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG

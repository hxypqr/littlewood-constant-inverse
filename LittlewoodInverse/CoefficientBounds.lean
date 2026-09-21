import LittlewoodInverse.CoefficientValues

open scoped BigOperators
namespace LittlewoodInverse.MomentCertificate
open SincFormula
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def coefficientBound : ℕ → ℚ
  | 0 => (605530070819498333084507 : ℚ) / 1000000000000000000000000
  | 1 => (550000000000000000000000 : ℚ) / 1000000000000000000000000
  | 2 => (513469369729873615168791 : ℚ) / 1000000000000000000000000
  | 3 => (479365079365079365079366 : ℚ) / 1000000000000000000000000
  | 4 => (454232592376835342069117 : ℚ) / 1000000000000000000000000
  | 5 => (430417768959435626102293 : ℚ) / 1000000000000000000000000
  | 6 => (411767607879677092342742 : ℚ) / 1000000000000000000000000
  | 7 => (393925565175565175565176 : ℚ) / 1000000000000000000000000
  | 8 => (379379659787849804235399 : ℚ) / 1000000000000000000000000
  | 9 => (365370869485452818786153 : ℚ) / 1000000000000000000000000
  | 10 => (353616489808280089471048 : ℚ) / 1000000000000000000000000
  | 11 => (342240261355340720420086 : ℚ) / 1000000000000000000000000
  | 12 => (332485818459256248555786 : ℚ) / 1000000000000000000000000
  | 13 => (323009394156998706631060 : ℚ) / 1000000000000000000000000
  | 14 => (314745536877834806313489 : ℚ) / 1000000000000000000000000
  | 15 => (306693101737982424530517 : ℚ) / 1000000000000000000000000
  | 16 => (299575298691184212434433 : ℚ) / 1000000000000000000000000
  | 17 => (292622687231434779186401 : ℚ) / 1000000000000000000000000
  | 18 => (286408459234390315179995 : ℚ) / 1000000000000000000000000
  | 19 => (280326198549807544976356 : ℚ) / 1000000000000000000000000
  | 20 => (274839286373083133780467 : ℚ) / 1000000000000000000000000
  | 21 => (269459771240911935947803 : ℚ) / 1000000000000000000000000
  | 22 => (264568567340679437131269 : ℚ) / 1000000000000000000000000
  | 23 => (259766148031495449005129 : ℚ) / 1000000000000000000000000
  | 24 => (255370134722379739202038 : ℚ) / 1000000000000000000000000
  | 25 => (251048514990565639129980 : ℚ) / 1000000000000000000000000
  | 26 => (247069418691719419516841 : ℚ) / 1000000000000000000000000
  | 27 => (243153390709991453691134 : ℚ) / 1000000000000000000000000
  | 28 => (239529229358052442814368 : ℚ) / 1000000000000000000000000
  | 29 => (235959085535815717456299 : ℚ) / 1000000000000000000000000
  | 30 => (232640053628818441391740 : ℚ) / 1000000000000000000000000
  | 31 => (229367707666440127178472 : ℚ) / 1000000000000000000000000
  | 32 => (226313264130048179780394 : ℚ) / 1000000000000000000000000
  | 33 => (223299496002640021111360 : ℚ) / 1000000000000000000000000
  | 34 => (220476260331772005629706 : ℚ) / 1000000000000000000000000
  | 35 => (217688719589893741822523 : ℚ) / 1000000000000000000000000
  | 36 => (215068923873437702484922 : ℚ) / 1000000000000000000000000
  | 37 => (212480656339098271289704 : ℚ) / 1000000000000000000000000
  | 38 => (210040987543860965897637 : ℚ) / 1000000000000000000000000
  | 39 => (207629330634190108790509 : ℚ) / 1000000000000000000000000
  | 40 => (205350051967607839082690 : ℚ) / 1000000000000000000000000
  | 41 => (203095794386553654084526 : ℚ) / 1000000000000000000000000
  | 42 => (200960069570096998005355 : ℚ) / 1000000000000000000000000
  | 43 => (198846803714474101112355 : ℚ) / 1000000000000000000000000
  | 44 => (196840171019595891366656 : ℚ) / 1000000000000000000000000
  | 45 => (194853787957585484620895 : ℚ) / 1000000000000000000000000
  | 46 => (192963746296583987605020 : ℚ) / 1000000000000000000000000
  | 47 => (191092037650905235475819 : ℚ) / 1000000000000000000000000
  | 48 => (189307717561325375025980 : ℚ) / 1000000000000000000000000
  | 49 => (187540058543662569404965 : ℚ) / 1000000000000000000000000
  | 50 => (185851958228380312876920 : ℚ) / 1000000000000000000000000
  | 51 => (184179052974337693311432 : ℚ) / 1000000000000000000000000
  | 52 => (182578824722731320442443 : ℚ) / 1000000000000000000000000
  | 53 => (180992499954805016144850 : ℚ) / 1000000000000000000000000
  | 54 => (179472775961718972713112 : ℚ) / 1000000000000000000000000
  | 55 => (177965812502996165883602 : ℚ) / 1000000000000000000000000
  | 56 => (176520061775326892295522 : ℚ) / 1000000000000000000000000
  | 57 => (175086055972916907169592 : ℚ) / 1000000000000000000000000
  | 58 => (173708465972616269931717 : ℚ) / 1000000000000000000000000
  | 59 => (172341714952029824569858 : ℚ) / 1000000000000000000000000
  | 60 => (171027093075874833634456 : ℚ) / 1000000000000000000000000
  | 61 => (169722499129857048945914 : ℚ) / 1000000000000000000000000
  | 62 => (168466190213023576945493 : ℚ) / 1000000000000000000000000
  | 63 => (167219180664880803419246 : ℚ) / 1000000000000000000000000
  | 64 => (166016997516742293542765 : ℚ) / 1000000000000000000000000
  | 65 => (164823457182878568275823 : ℚ) / 1000000000000000000000000
  | 66 => (163671621789899381752419 : ℚ) / 1000000000000000000000000
  | 67 => (162527835765591351422718 : ℚ) / 1000000000000000000000000
  | 68 => (161422929277999549608842 : ℚ) / 1000000000000000000000000
  | 69 => (160325534232005254817514 : ℚ) / 1000000000000000000000000
  | 70 => (159264454224445661538512 : ℚ) / 1000000000000000000000000
  | 71 => (158210396746315556408293 : ℚ) / 1000000000000000000000000
  | 72 => (157190320534406580790246 : ℚ) / 1000000000000000000000000
  | 73 => (156176821358517374827753 : ℚ) / 1000000000000000000000000
  | 74 => (155195174382680054633774 : ℚ) / 1000000000000000000000000
  | 75 => (154219697533605389306791 : ℚ) / 1000000000000000000000000
  | 76 => (153274126003195716019876 : ℚ) / 1000000000000000000000000
  | 77 => (152334352081868543110602 : ℚ) / 1000000000000000000000000
  | 78 => (151422699217379853750460 : ℚ) / 1000000000000000000000000
  | 79 => (150516502186942854657924 : ℚ) / 1000000000000000000000000
  | 80 => (149636787514047261998940 : ℚ) / 1000000000000000000000000
  | 81 => (148762214456153767989599 : ℚ) / 1000000000000000000000000
  | 82 => (147912615698850146186390 : ℚ) / 1000000000000000000000000
  | 83 => (147067869101424963187883 : ℚ) / 1000000000000000000000000
  | 84 => (146246706297326191577275 : ℚ) / 1000000000000000000000000
  | 85 => (145430128507989348166008 : ℚ) / 1000000000000000000000000
  | 86 => (144635850030490379955137 : ℚ) / 1000000000000000000000000
  | 87 => (143845909569510343865171 : ℚ) / 1000000000000000000000000
  | 88 => (143077079792083550172548 : ℚ) / 1000000000000000000000000
  | 89 => (142312359267595732110256 : ℚ) / 1000000000000000000000000
  | 90 => (141567647646986865156731 : ℚ) / 1000000000000000000000000
  | 91 => (140826833055425398483106 : ℚ) / 1000000000000000000000000
  | 92 => (140105004444819613872949 : ℚ) / 1000000000000000000000000
  | 93 => (139386875672744487780133 : ℚ) / 1000000000000000000000000
  | 94 => (138686781704416091671003 : ℚ) / 1000000000000000000000000
  | 95 => (137990204075500026911848 : ℚ) / 1000000000000000000000000
  | 96 => (137310775476145971299918 : ℚ) / 1000000000000000000000000
  | 97 => (136634692210069107169388 : ℚ) / 1000000000000000000000000
  | 98 => (135974931931827058457670 : ℚ) / 1000000000000000000000000
  | 99 => (135318357401052986607995 : ℚ) / 1000000000000000000000000
  | 100 => (134677334467818933084983 : ℚ) / 1000000000000000000000000
  | 101 => (134039348154366733286429 : ℚ) / 1000000000000000000000000
  | 102 => (133416192137017109317040 : ℚ) / 1000000000000000000000000
  | 103 => (132795933204943607634215 : ℚ) / 1000000000000000000000000
  | 104 => (132189829250887576196674 : ℚ) / 1000000000000000000000000
  | 105 => (131586491661691193036716 : ℚ) / 1000000000000000000000000
  | 106 => (130996676014199271283668 : ℚ) / 1000000000000000000000000
  | 107 => (130409504122108327319730 : ℚ) / 1000000000000000000000000
  | 108 => (129835260073384953756009 : ℚ) / 1000000000000000000000000
  | 109 => (129263544645790186329268 : ℚ) / 1000000000000000000000000
  | 110 => (128704198875026441341443 : ℚ) / 1000000000000000000000000
  | 111 => (128147273490398080560194 : ℚ) / 1000000000000000000000000
  | 112 => (127602192744258937516105 : ℚ) / 1000000000000000000000000
  | 113 => (127059430525948900935386 : ℚ) / 1000000000000000000000000
  | 114 => (126528018604283935282193 : ℚ) / 1000000000000000000000000
  | 115 => (125998829253815131084422 : ℚ) / 1000000000000000000000000
  | 116 => (125480524267970578266568 : ℚ) / 1000000000000000000000000
  | 117 => (124964351365891741771177 : ℚ) / 1000000000000000000000000
  | 118 => (124458623240959754459005 : ℚ) / 1000000000000000000000000
  | 119 => (123954941787206800947316 : ℚ) / 1000000000000000000000000
  | 120 => (123461289982970141991168 : ℚ) / 1000000000000000000000000
  | 121 => (122969604152016294577955 : ℚ) / 1000000000000000000000000
  | 122 => (122487555580313242643426 : ℚ) / 1000000000000000000000000
  | 123 => (122007396669287586182889 : ℚ) / 1000000000000000000000000
  | 124 => (121536503788099338790710 : ℚ) / 1000000000000000000000000
  | 125 => (121067428338571852229992 : ℚ) / 1000000000000000000000000
  | 126 => (120607267405379339540534 : ℚ) / 1000000000000000000000000
  | 127 => (120148855481704435821298 : ℚ) / 1000000000000000000000000
  | 128 => (119699024950620537168313 : ℚ) / 1000000000000000000000000
  | 129 => (119250878559646704188036 : ℚ) / 1000000000000000000000000
  | 130 => (118810997608543389269967 : ℚ) / 1000000000000000000000000
  | 131 => (118372739247172583322891 : ℚ) / 1000000000000000000000000
  | 132 => (117942446422524378885801 : ℚ) / 1000000000000000000000000
  | 133 => (117513717741074357242275 : ℚ) / 1000000000000000000000000
  | 134 => (117092669709558567755744 : ℚ) / 1000000000000000000000000
  | 135 => (116673130280172394634792 : ℚ) / 1000000000000000000000000
  | 136 => (116261000677227211415047 : ℚ) / 1000000000000000000000000
  | 137 => (115850326857710619543148 : ℚ) / 1000000000000000000000000
  | 138 => (115446805224275580173850 : ℚ) / 1000000000000000000000000
  | 139 => (115044689108745121881432 : ℚ) / 1000000000000000000000000
  | 140 => (114649479908312253798990 : ℚ) / 1000000000000000000000000
  | 141 => (114255628356922699216980 : ℚ) / 1000000000000000000000000
  | 142 => (113868450065826471651399 : ℚ) / 1000000000000000000000000
  | 143 => (113482583806629695911183 : ℚ) / 1000000000000000000000000
  | 144 => (113103168071212829085852 : ℚ) / 1000000000000000000000000
  | 145 => (112725020867895365445850 : ℚ) / 1000000000000000000000000
  | 146 => (112353111722816990786156 : ℚ) / 1000000000000000000000000
  | 147 => (111982429602680621000534 : ℚ) / 1000000000000000000000000
  | 148 => (111617782745193080509035 : ℚ) / 1000000000000000000000000
  | 149 => (111254323282291881049291 : ℚ) / 1000000000000000000000000
  | 150 => (110896705397811101082696 : ℚ) / 1000000000000000000000000
  | 151 => (110540237046647565827234 : ℚ) / 1000000000000000000000000
  | 152 => (110189425181386810569252 : ℚ) / 1000000000000000000000000
  | 153 => (109839726657006225449314 : ℚ) / 1000000000000000000000000
  | 154 => (109495507633840529143179 : ℚ) / 1000000000000000000000000
  | 155 => (109152367334552935171958 : ℚ) / 1000000000000000000000000
  | _ => 0

theorem coefficientBound_valid (j : ℕ) (hj : j < 156) :
    momentCoefficient (j + 5) ≤ (coefficientBound j : ℝ) := by
  interval_cases j
  · convert coefficient_le_5 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_6 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_7 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_8 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_9 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_10 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_11 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_12 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_13 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_14 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_15 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_16 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_17 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_18 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_19 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_20 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_21 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_22 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_23 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_24 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_25 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_26 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_27 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_28 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_29 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_30 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_31 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_32 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_33 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_34 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_35 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_36 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_37 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_38 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_39 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_40 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_41 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_42 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_43 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_44 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_45 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_46 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_47 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_48 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_49 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_50 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_51 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_52 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_53 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_54 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_55 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_56 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_57 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_58 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_59 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_60 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_61 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_62 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_63 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_64 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_65 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_66 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_67 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_68 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_69 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_70 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_71 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_72 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_73 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_74 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_75 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_76 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_77 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_78 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_79 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_80 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_81 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_82 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_83 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_84 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_85 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_86 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_87 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_88 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_89 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_90 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_91 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_92 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_93 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_94 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_95 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_96 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_97 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_98 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_99 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_100 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_101 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_102 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_103 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_104 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_105 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_106 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_107 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_108 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_109 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_110 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_111 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_112 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_113 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_114 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_115 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_116 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_117 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_118 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_119 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_120 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_121 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_122 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_123 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_124 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_125 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_126 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_127 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_128 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_129 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_130 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_131 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_132 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_133 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_134 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_135 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_136 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_137 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_138 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_139 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_140 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_141 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_142 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_143 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_144 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_145 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_146 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_147 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_148 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_149 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_150 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_151 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_152 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_153 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_154 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_155 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_156 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_157 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_158 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_159 using 1
    norm_num [coefficientBound]
  · convert coefficient_le_160 using 1
    norm_num [coefficientBound]
end LittlewoodInverse.MomentCertificate

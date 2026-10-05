/**
 * PDD 3D Simulator Game Engine
 * Built with Three.js (Isometric View, Low-Poly Stylization, Procedural Road & PDD Situations)
 */

(function() {
  'use strict';

  // --- Constants & Brand Colors ---
  const BRAND = {
    accent: 0x0574F8,
    accentLight: 0xE8F2FE,
    green: 0x2BC280,
    greenLight: 0xE8F8F0,
    red: 0xED4621,
    redLight: 0xFFFFECE8,
    gold: 0xFFA53C,
    asphalt: 0x2C2F36,
    asphaltMarking: 0xF2F4F8,
    asphaltMarkingYellow: 0xF5B025,
    grass: 0x496D42,
    grassDark: 0x3D5C38,
    sidewalk: 0x747970,
    curb: 0x737870,
    buildingColors: [0xF5F6FA, 0xE9ECF2, 0xDDE1EA, 0xC6CCD8],
    windowColor: 0x64748B,
    playerCar: 0xED4621, // Red car as in reference
    tramRed: 0xD32F2F,
    tramWhite: 0xF5F5F5
  };

  // --- Game State ---
  const ENVIRONMENT_GROUND = 0x86A97A;
  // Seasons follow the player's calendar (debug override via setSeason).
  // Each one tints ground, pavement, roofs and tree canopies, sets the light
  // and sky mood and decides what falls from the sky.
  const SEASONS = {
    summer: { ground: 0x86A97A, verge: [0x86A97A, 0x86A97A, 0x86A97A], sky: 0xDEE4E5, skyDark: 0x252B30,
      sun: 0xFFF9EE, sunIntensity: 0.6, ambient: 0.72, canopy: [0x4C9A4F, 0x3F8A46, 0x7FB069, 0x5FA85A],
      birch: 0x7FB069, pine: [0x388E3C, 0x43A047], roof: null, sidewalk: 0x747970, precipitation: 'rain', hillColor: 0x6E8F63 },
    autumn: { ground: 0x9CA56A, verge: [0x9CA56A, 0x9CA56A, 0x9CA56A], sky: 0xE8E1D1, skyDark: 0x2A2823,
      sun: 0xFFE3B8, sunIntensity: 0.56, ambient: 0.7, canopy: [0xD98A2B, 0xC94F2B, 0xE0B33C, 0xB86A2A, 0xC7A24A],
      birch: 0xE0B33C, pine: [0x3E7C42, 0x467E3C], roof: null, sidewalk: 0x7A776F, precipitation: 'rain', hillColor: 0x8E8A55 },
    winter: { ground: 0xE4E8EC, verge: [0xE4E8EC, 0xE4E8EC, 0xE4E8EC], sky: 0xE1E6EB, skyDark: 0x20262C,
      sun: 0xEAF1FA, sunIntensity: 0.5, ambient: 0.82, canopy: [0x8A7A66, 0x9C8B78, 0xBDC6CC, 0x8C8578],
      birch: 0xB9C4CC, pine: [0x3A6B45, 0x40704A], roof: 0xC7D0D8, sidewalk: 0xB9C0C6, precipitation: 'snow', hillColor: 0xD8DEE3 },
  };
  function seasonFromDate() {
    const m = new Date().getMonth() + 1;
    return m >= 9 && m <= 11 ? 'autumn' : (m === 12 || m <= 2) ? 'winter' : 'summer';
  }
  let currentSeason = SEASONS[seasonFromDate()];
  const season = () => currentSeason;
  // The HUD draws its bare numbers dark over snow in either UI theme.
  const seasonName = () => Object.keys(SEASONS).find(k => SEASONS[k] === currentSeason);
  const state = {
    speed: 0,
    maxSpeed: 18, // m/s, follows the speed limit in force (see effectiveLimitKmH)
    baseLimitKmH: 60, // built-up area unless a sign says otherwise
    busBays: [], // bus bays in the world; walkers detour round them
    humps: [], // speed humps (5.20) the player's car rides over
    props: [], // knockable cones / barriers of road works
    flying: [], // props knocked loose, until they settle
    crews: [], // animated road-works crews
    acceleration: 24, // m/s^2
    braking: 35, // m/s^2
    coasting: 10, // m/s^2
    isAccelerating: false,
    distanceTraveled: 0,
    targetLane: 1, // 0 = left, 1 = right
    currentLaneOffset: -1.8,
    targetLaneOffset: -1.8,
    laneWidth: 3.6,
    isAtSituation: false,
    isResolvingSituation: false,
    currentSituation: null,
    isDarkTheme: false,
    roadSegments: [],
    intersections: [],
    activeIntersection: null,
    actors: [],
    splinePoints: [],
    spline: null,
    splineLength: 0,
    carSplineDist: 0,
    score: 0
  };
  state.paused = false;
  state.oncoming = false;
  state.violationEpisode = 0;
  state.oncomingSeconds = 0;
  state.oncomingPenalized = false;
  state.resolution = null;
  state.driveFaults = new Set();
  state.lastSafePosition = new THREE.Vector3(-1.8, 0, 0);
  state.driveRecovery = 0;
  state.ambient = [];
  state.occluders = [];
  state.district = 0;
  // park / homes / boulevard / high-rise blocks
  const DISTRICTS = 4;
  state.viewportInsets = { top: 64, bottom: 150 };
  state.labels = { player: 'ВЫ' };
  const signTextureCache = new Map();

  // --- Three.js Globals ---
  let scene, camera, renderer;
  let dirLight, ambientLight, sunTarget;
  let playerCarGroup, playerWheels = [];
  let rainParticles = null;
  let terrainMesh = null;
  let streetLights = [];
  let nextSegmentZ = 0;
  let currentCorridor = null;
  let situationIndex = 0;
  let situationBag = [], lastSituationId = null;
  let container = document.getElementById('canvas-container');
  let gameAudio = null;

  // --- Situations Database (MVP set matching Russian PDD tickets) ---
  const SITUATIONS = [
  {
    "id": "ticket_1_13",
    "ticket": "Билет 1 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "При повороте направо Вы должны уступить дорогу:",
    "explanation": "При повороте направо или налево водитель обязан уступить дорогу пешеходам, переходящим проезжую часть дороги, на которую он поворачивает, лицам, использующим для передвижения средства индивидуальной мобильности (далее СИМ) и велосипедистам, независимо от того, регулируемый или нерегулируемый это перекресток.(Пункт 13.1 ПДД)",
    "pddRule": "п. 13.1",
    "options": [
      "Только велосипедисту",
      "Только пешеходам",
      "Пешеходам и велосипедисту",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы направо",
        "color": "#ED4621"
      },
      {
        "label": "Велосипедист",
        "color": "#2BC280"
      },
      {
        "label": "Пешеход",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "cyclist",
        "id": "cyclist",
        "name": "Велосипедист",
        "badge": "Вело",
        "side": "cross_right_edge",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "type": "pedestrian",
        "id": "pedestrian",
        "name": "Пешеход",
        "badge": "Пешеход",
        "side": "crosswalk_right",
        "targetAction": "cross",
        "color": "#0574F8"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_1_14",
    "ticket": "Билет 1 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "Вы намерены проехать перекресток в прямом направлении. Кому Вы должны уступить дорогу?",
    "explanation": "Перекрёсток равнозначный. Трамваи в равнозначных условиях имеют преимущество перед безрельсовыми транспортными средствами. Между собой руководствуются «правилом правой руки». Помеха справа у трамвая «А». Соответственно первым проезжает трамвай «Б», за ним «А», Вы последним.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Обоим трамваям",
      "Только трамваю А",
      "Только трамваю Б",
      "Никому"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай А",
        "color": "#0574F8"
      },
      {
        "label": "Трамвай Б",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_b",
        "name": "Трамвай Б",
        "badge": "Б",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "type": "tram",
        "id": "tram_a",
        "name": "Трамвай А",
        "badge": "А",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_1_15",
    "ticket": "Билет 1 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, а водители между собой руководствуются «правилом правой руки». Никому не уступая, первым проезжаете Вы, вторым автобус, легковой автомобиль последним, так как он находится на второстепенной дороге.(«Дорожные знаки», пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "bus",
        "id": "npc_bus",
        "name": "Автобус",
        "badge": "Автобус",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "badge": "Авто",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_2_13",
    "ticket": "Билет 2 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены повернуть налево. Кому Вы должны уступить дорогу?",
    "explanation": "Перекрёсток регулируемый. Знаки приоритета «не работают». При повороте налево Вы уступаете автобусу, движущемуся прямо со встречного направления, и пешеходам, переходящим проезжую часть дороги, на которую Вы поворачиваете.(Пункты 13.1, 13.3, 13.4 ПДД).",
    "pddRule": "п. 13.4",
    "options": [
      "Только пешеходам",
      "Только автобусу",
      "Автобусу и пешеходам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Пешеход",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "bus",
        "id": "npc_bus",
        "name": "Автобус",
        "badge": "Автобус",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "type": "pedestrian",
        "id": "pedestrian",
        "name": "Пешеход",
        "badge": "Пешеход",
        "side": "crosswalk_left",
        "targetAction": "cross",
        "color": "#0574F8"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_2_14",
    "ticket": "Билет 2 · Вопрос 14",
    "type": "crossroad",
    "title": "В каком случае Вы имеете преимущество?",
    "explanation": "Перекресток равнозначный. Водители между собой руководствуются «правилом правой руки», т. е. у кого помеха справа, тот и уступает. У Вас преимущество и при повороте направо и при повороте налево, т. е. в обоих перечисленных случаях.(Пункт 13.11 ПДД).",
    "pddRule": "п. 13.11",
    "options": [
      "Только при повороте направо",
      "Только при повороте налево",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "badge": "Встречный",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_2_15",
    "ticket": "Билет 2 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Обязан ли водитель мотоцикла уступить Вам дорогу?",
    "explanation": "Мотоциклист выезжает на дорогу, обозначенную знаком 5.1 «Автомагистраль», которая является главной дорогой по отношению к примыкающей. На перекрёстке неравнозначных дорог преимущество имеют транспортные средства, движущиеся по главной дороге. Мотоциклист обязан уступить Вам дорогу.(Пункты 1.2, 13.9 ПДД).",
    "pddRule": "п. 13.9",
    "options": [
      "Обязан",
      "Не обязан"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Мотоцикл",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "motorcycle",
        "id": "npc_moto",
        "name": "Мотоцикл",
        "badge": "Мото",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_3_13",
    "ticket": "Билет 3 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "При движении прямо Вы:",
    "explanation": "Перекрёсток регулируемый. В этом случае знаки приоритета, а в их число входит и знак 2.5 «Движение без остановки запрещено», согласно принципу приоритетности регулирования дорожного движения, «не работают», т.е. ими мы не руководствуемся. Горит зелёный сигнал светофора. Продолжаете движение через перекрёсток без остановки.(Пункты 6.2, 6.15, 13.3 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Должны остановиться перед стоп-линией",
      "Можете продолжить движение через перекрёсток без остановки",
      "Должны уступить дорогу транспортным средствам, движущимся с других направлений"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль слева",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "badge": "Авто",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": [
      {
        "code": "2.5",
        "name": "STOP"
      }
    ]
  },
  {
    "id": "ticket_3_14",
    "ticket": "Билет 3 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены повернуть направо. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. Водители при определении порядка проезда перекрёстка руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает дорогу. У Вас помехи справа при повороте направо нет, т.к. при повороте направо Ваша траектория не пересекается с мотоциклом. Проезжаете перекресток первым.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекрёсток первым",
      "Уступите дорогу легковому автомобилю",
      "Уступите дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы направо",
        "color": "#ED4621"
      },
      {
        "label": "Легковой авто",
        "color": "#2BC280"
      },
      {
        "label": "Мотоцикл",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Легковой авто",
        "badge": "Авто",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#2BC280"
      },
      {
        "type": "motorcycle",
        "id": "npc_moto",
        "name": "Мотоцикл",
        "badge": "Мото",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_3_15",
    "ticket": "Билет 3 · Вопрос 15",
    "type": "crossroad_tram",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество; между собой безрельсовые транспортные средства руководствуются «правилом правой руки», уступая трамваю, имеющему преимущество в равнозначных условиях. Трамвай «А» проезжает первым, Вы после него. Легковой автомобиль и трамвай «Б» одновременно, так как их траектории не пересекаются.(«Дорожные знаки», пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Трамваям А и Б",
      "Трамваю А и легковому автомобилю",
      "Только трамваю А",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай А",
        "color": "#0574F8"
      },
      {
        "label": "Трамвай Б",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_a",
        "name": "Трамвай А",
        "badge": "А",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#0574F8"
      },
      {
        "type": "tram",
        "id": "tram_b",
        "name": "Трамвай Б",
        "badge": "Б",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "badge": "Авто",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_4_13",
    "ticket": "Билет 4 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Ваши действия?",
    "explanation": "Перекресток регулируемый. Первым проедет «оперативник» со специальными сигналами, который может отступать от требований сигналов светофора. Другие водители должны обеспечить ему беспрепятственный проезд перекрёстка. Водитель грузовика обязан уступить Вам, т.е. транспортному средству, движущемуся прямо со встречного направления.(Пункты 3.1, 3.2, 13.3, 13.4 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Проедете перекресток первым",
      "Уступите дорогу только встречному автомобилю",
      "Уступите дорогу только автомобилю с включенными проблесковым маячком и специальным звуковым сигналом",
      "Уступите дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Спецмашина",
        "color": "#0574F8"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "special",
        "id": "npc_special",
        "name": "Спецмашина",
        "badge": "Спец",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8"
      },
      {
        "type": "truck",
        "id": "npc_truck",
        "name": "Грузовик",
        "badge": "Грузовик",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_4_14",
    "ticket": "Билет 4 · Вопрос 14",
    "type": "crossroad_traffic_light",
    "title": "Кому Вы должны уступить дорогу при повороте направо?",
    "explanation": "Первоначально Вы должны уступить дорогу пешеходу, находящемуся на нерегулируемом пешеходном переходе. (Пункт 14.1 ПДД). В последующем, при повороте направо уступите дорогу пешеходам, переходящим проезжую часть дороги, на которую Вы поворачиваете. (Пункт 13.1 ПДД). Так же Вы должны поступить и с лицами, использующими для передвижения СИМ. Это правило распространяется при проезде как регулируемых, так и нерегулируемых перекрестков.",
    "pddRule": "п. 14.1",
    "options": [
      "Только пешеходу, переходящему проезжую часть по нерегулируемому пешеходному переходу",
      "Только пешеходам, переходящим проезжую часть, на которую Вы поворачиваете",
      "Всем пешеходам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы направо",
        "color": "#ED4621"
      },
      {
        "label": "Пешеход 1",
        "color": "#0574F8"
      },
      {
        "label": "Пешеход 2",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "pedestrian",
        "id": "ped_1",
        "name": "Пешеход",
        "badge": "Пешеход",
        "side": "crosswalk_right",
        "targetAction": "cross",
        "color": "#0574F8"
      },
      {
        "type": "pedestrian",
        "id": "ped_2",
        "name": "Пешеход",
        "badge": "Пешеход",
        "side": "crosswalk_left",
        "targetAction": "cross",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_4_15",
    "ticket": "Билет 4 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Как Вам следует поступить при выполнении разворота?",
    "explanation": "Перекрёсток неравнозначный. Транспортные средства, находящиеся на главной дороге, имеют преимущество. При повороте налево и развороте Вы уступаете дорогу транспортным средствам, движущимся прямо со встречного направления. В данной ситуации уступаете дорогу только легковому автомобилю.(Пункты 13.9, 13.12 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Проехать перекресток первым",
      "Уступить дорогу только легковому автомобилю",
      "Уступить дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы на разворот",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "badge": "Встречный",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_5_13",
    "ticket": "Билет 5 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены развернуться. Ваши действия?",
    "explanation": "Перекрёсток регулируемый. Правая рука регулировщика вытянута вперёд. Со стороны левого бока транспортные средства могут продолжить движение в любом направлении, соблюдая правила расположения транспортных средств на проезжей части.Производя разворот из крайней левой полосы, у Вас будет помеха справа. Вы уступите дорогу легковому автомобилю, поворачивающему направо. (Пункты 6.10, 13.4 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Проедете перекресток первым",
      "Выполните разворот, уступив дорогу легковому автомобилю",
      "Дождетесь, когда регулировщик опустит правую руку"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы на разворот",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "badge": "Авто",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_5_14",
    "ticket": "Билет 5 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "Кому Вы должны уступить дорогу при движении в прямом направлении?",
    "explanation": "Перекрёсток равнозначный. В равнозначных условиях трамвай имеет преимущество, а безрельсовые транспортные средства между собой руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает.Уступаете дорогу в данной ситуации только трамваю.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только трамваю",
      "Только легковому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      },
      {
        "label": "Легковой автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "badge": "Трамвай",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8"
      },
      {
        "type": "car",
        "id": "npc_car",
        "name": "Легковой автомобиль",
        "badge": "Авто",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_5_15",
    "ticket": "Билет 5 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Проблесковый маячок жёлтого цвета на грузовике преимущество ему не предоставляет. Преимущество имеют транспортные средства, находящиеся на главной дороге. Вы проезжаете первым, после Вас проезжают автомобили, находящиеся на второстепенной дороге, которые между собой руководствуются «правилом правой руки». Легковой автомобиль проедет вторым, грузовик - последним.(Пункты 3.4, 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу только грузовому автомобилю с включенным проблесковым маячком",
      "Уступить дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_6_13",
    "ticket": "Билет 6 · Вопрос 13",
    "type": "crossroad_tram",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Светофор с сигналами бело-лунного цвета, предназначенный для водителей маршрутных транспортных средств, разрешает им движение прямо.Согласно зелёного сигнала светофора, разрешено движение и Вам в любом направлении.Для поворота налево, Вы должны пропустить трамвай, перестроиться на трамвайные пути попутного направления и с них выполнить поворот налево. (Пункты 6.2, 6.8, 8.5).",
    "pddRule": "п. 13.4",
    "options": [
      "Проедете перекресток первым",
      "Уступите дорогу трамваю, выполнив поворот с проезжей части",
      "Пропустите трамвай, перестроитесь на трамвайные пути попутного направления и выполните с них поворот"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_6_14",
    "ticket": "Билет 6 · Вопрос 14",
    "type": "crossroad_traffic_light",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "На перекрёстках, независимо регулируемые они или нет, при повороте налево или направо водитель обязан уступить дорогу пешеходам, переходящим проезжую часть, на которую он поворачивает. Следует уступить и велосипедисту, движущемуся навстречу прямо.(Пункты 13.1, 13.2 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только пешеходам",
      "Пешеходам и велосипедисту",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_6_15",
    "ticket": "Билет 6 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "В каком случае Вы должны будете уступить дорогу автомобилю ДПС?",
    "explanation": "В данном случае Вы должны уступить дорогу «оперативнику», если на данном автомобиле одновременно будут включены проблесковые маячки синего цвета и специальный звуковой сигнал.(Пункт 3.2 ПДД)",
    "pddRule": "п. 3.2",
    "options": [
      "Если на автомобиле ДПС будут включены проблесковые маячки синего цвета",
      "Если на автомобиле ДПС одновременно будут включены проблесковые маячки синего цвета и специальный звуковой сигнал",
      "В любом"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_7_13",
    "ticket": "Билет 7 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Остановка не далее стоп-линии обязательна при запрещающем сигнале светофора. Вам же горит «зелёный». Без остановки выезжаете на перекрёсток и перед поворотом налево останавливаетесь, чтобы уступить дорогу легковому автомобилю, движущемуся прямо со встречного направления.(«Горизонтальная разметка», пункты 6.13, 6.2, 13.3, 13.4 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Проехать перекресток первым",
      "Выехать за стоп-линию и остановиться на перекрестке, чтобы уступить дорогу встречному автомобилю",
      "Остановиться перед стоп-линией и после проезда легкового автомобиля повернуть налево"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_7_14",
    "ticket": "Билет 7 · Вопрос 14",
    "type": "crossroad",
    "title": "Разрешено ли Вам выехать на перекресток, за которым образовался затор?",
    "explanation": "В данной ситуации Вы можете выехать на перекресток только для поворота, так как образовавшийся затор делает невозможным движение в прямом направлении без вынужденной остановки на перекрестке, а это создаст препятствие для движения в поперечном направлении.(Пункт 13.2 ПДД).",
    "pddRule": "п. 13.2",
    "options": [
      "Разрешено",
      "Разрешено, если Вы намерены выполнить поворот",
      "Запрещено"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_7_15",
    "ticket": "Билет 7 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены продолжить движение прямо. Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, между собой руководствуются «правилом правой руки». После их проезда, пользуясь этим же правилом, проезжают транспортные средства, находящиеся на второстепенной дороге. Первым проезжаете Вы, никому не уступая, мотоциклист – вторым, грузовик – третьим, легковой автомобиль – последним.(«Дорожные знаки», пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только мотоциклу",
      "Мотоциклу и легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_8_13",
    "ticket": "Билет 8 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Кто из водителей, выполняющих поворот, нарушит Правила?",
    "explanation": "Знак 4.1.1 «Движение прямо» в данном случае установлен непосредственно перед пересечением проезжих частей, т.е перед перекрестком. Можно продолжать движение только прямо. В данной ситуации нарушают Правила оба водителя.(«Дорожные знаки»)",
    "pddRule": "п. 13.4",
    "options": [
      "Оба",
      "Только водитель легкового автомобиля",
      "Только водитель мотоцикла",
      "Никто не нарушит"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_8_14",
    "ticket": "Билет 8 · Вопрос 14",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены продолжить движение в прямом направлении. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. При определении порядка проезда перекрёстка транспортными средствами руководствуемся «правилом правой руки», т.е. у кого помеха справа тот и уступает. Особенность решения этого вопроса - в выкатывании и остановке на перекрёстке транспортного средства, начинающего движение. Первым начинает движение водитель легкового автомобиля, поворачивающий налево, поскольку он в первоначальный момент не имеет помехи справа. Доехав до середины перекрёстка, перед тем как повернуть налево, он остановится, так как должен уступить дорогу мотоциклисту, находящемуся от него справа. После этого на траектории движения Вашего автомобиля помеха справа будет отсутствовать - проезжаете перекрёсток первым. Мотоциклист после Вас. И последним закончит проезд перекрёстка водитель, который начинал движение.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекресток первым",
      "Уступите дорогу легковому автомобилю",
      "Уступите дорогу легковому автомобилю и мотоциклу"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_8_15",
    "ticket": "Билет 8 · Вопрос 15",
    "type": "crossroad_tram",
    "title": "Кому Вы должны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество. Между собой безрельсовые транспортные средства руководствуются «правилом правой руки», уступая дорогу трамваю, который в равнозначных условиях имеет перед ними преимущество. Первым проезжает трамвай «Б», после него легковой автомобиль, Вы после них. Последним проедет трамвай «А», так как он находится на второстепенной дороге.(Пункты 13.9, 13.1, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только трамваям",
      "Трамваю Б и легковому автомобилю",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_9_13",
    "ticket": "Билет 9 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Разрешено ли Вам выехать на перекресток, за которым образовался затор?",
    "explanation": "Перекрёсток регулируемый. Вам «зелёный свет», но впереди «пробка». Если Вы выедете на перекрёсток для движения в прямом направлении, то при смене сигналов будете оказывать помехи движению, особенно в поперечном направлении. Поэтому на перекрёсток Вы можете выехать только для поворота направо или налево.(Пункты 6.2, 13.2 ПДД).(14.12.18 обновлен вариант ответа (правильный). Теперь нельзя выезжать на перекресток с затором, если вы собираетесь сделать разворот)",
    "pddRule": "п. 13.4",
    "options": [
      "Разрешено",
      "Разрешено, если Вы намерены выполнить поворот",
      "Запрещено"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_9_14",
    "ticket": "Билет 9 · Вопрос 14",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены продолжить движение в прямом направлении. Ваши действия?",
    "explanation": "Перекрёсток нерегулируемый, равнозначный. При разводке транспортных средств руководствуемся «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Вы обязаны уступить дорогу грузовику.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекресток первым",
      "Уступите дорогу грузовому автомобилю"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_9_15",
    "ticket": "Билет 9 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество. А между собой руководствуются «правилом правой руки». У Вас помехи справа нет. Проезжаете первым, водитель легкового автомобиля после Вас, автобус последним, так как находится на второстепенной дороге.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_10_13",
    "ticket": "Билет 10 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "При включении зелёного сигнала светофора Вам следует:",
    "explanation": "Грузовик закрывает обзорность справа, откуда могут неожиданно появиться пешеходы, начавшие движение после смены сигнала светофора. Следует убедиться в отсутствии ТС, завершающих движение через перекресток. Поэтому поступите с максимальной осторожностью.(Пункт 13.8 ПДД)",
    "pddRule": "п. 13.8",
    "options": [
      "Сразу начать движение",
      "Начать движение, убедившись в отсутствии только пешеходов, завершающих переход проезжей части",
      "Начать движение, убедившись в отсутствии пешеходов и транспортных средств, завершающих движение после смены сигнала светофора"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_10_14",
    "ticket": "Билет 10 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток равнозначный. В равнозначных условиях трамвай имеет преимущество, а безрельсовые транспортные средства руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Вы уступаете и трамваю, и грузовому автомобилю, которые проедут перекрёсток одновременно, т.к. их траектории движения не пересекаются.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только трамваю",
      "Только грузовому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_10_15",
    "ticket": "Билет 10 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы должны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимуществом пользуются транспортные средства, находящиеся на главной дороге, которые между собой руководствуются «правилом правой руки». Вы проезжаете первым, так как для легкового автомобиля Вы являетесь помехой справа, а автобус находится на второстепенной дороге.(Пункты 13.3, 13.10 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_11_13",
    "ticket": "Билет 11 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Обязаны ли Вы при повороте направо уступить дорогу автомобилю, выполняющему разворот?",
    "explanation": "При движении «под дополнительную секцию», включённую одновременно с основным красным сигналом светофора, Вы обязаны уступить дорогу ВСЕМ движущимся с других направлений, независимо от их дальнейшего направления движения.(Пункт 13.5 ПДД)",
    "pddRule": "п. 13.5",
    "options": [
      "Обязаны",
      "Не обязаны"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_11_14",
    "ticket": "Билет 11 · Вопрос 14",
    "type": "crossroad",
    "title": "В каком случае Вы имеете право проехать перекресток первым?",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Помеха справа у водителя легкового автомобиля. Вы проезжаете перекрёсток первым при движении прямо и налево. При развороте у Вас справа будет помеха.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только при движении прямо",
      "При движении прямо и налево",
      "При движении прямо, налево и в обратном направлении"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_11_15",
    "ticket": "Билет 11 · Вопрос 15",
    "type": "crossroad_tram",
    "title": "Вы намерены продолжить движение прямо. При жёлтом мигающем сигнале светофора следует:",
    "explanation": "При жёлтом мигающем сигнале светофора перекрёсток является нерегулируемым. Согласно знакам приоритета – неравнозначным. Транспортные средства, находящиеся на главной дороге, имеют преимущество. Вы проезжаете первым, никому не уступая, так как трамвай и грузовик находятся на второстепенной дороге.(Пункты 13.3, 13.9 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу только грузовому автомобилю",
      "Уступить дорогу только трамваю",
      "Уступить дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_12_13",
    "ticket": "Билет 12 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены повернуть направо. Ваши действия?",
    "explanation": "Руки регулировщика опущены («Грудь, спина – стена»). Со стороны правого и левого бока разрешено движение безрельсовым транспортным средствам прямо и направо, пешеходам разрешено переходить проезжую часть. (Пункт 6.10 ПДД). При повороте направо вы обязаны уступить дорогу пешеходам, переходящим проезжую часть дороги, на которую поворачиваете.(Пункт 13.1 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Повернете направо, не уступая дорогу пешеходам",
      "Повернете направо, уступив дорогу пешеходам",
      "Остановитесь перед перекрестком и дождетесь другого сигнала регулировщика"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_12_14",
    "ticket": "Билет 12 · Вопрос 14",
    "type": "crossroad_priority_signs",
    "title": "При движении в каком направлении Вы должны уступить дорогу автомобилю с включенными проблесковым маячком и специальным звуковым сигналом?",
    "explanation": "Вы обязаны обеспечить беспрепятственный проезд перекрёстка «оперативнику» с включенными специальными сигналами независимо от направления его движения. Сделать это необходимо при движении в любом направлении.(Пункты 3.1, 3.2 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только налево",
      "Налево и в обратном направлении",
      "В любом"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_12_15",
    "ticket": "Билет 12 · Вопрос 15",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены продолжить движение прямо. Ваши действия при жёлтом мигающем сигнале светофора?",
    "explanation": "При жёлтом мигающем сигнале светофора перекрёсток является нерегулируемым, неравнозначным. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге, которые между собой руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. У Вас помеха справа, уступаете дорогу только легковому автомобилю.(«Дорожные знаки», пункты 13.3, 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Уступите дорогу обоим транспортным средствам",
      "Уступите дорогу только трамваю",
      "Уступите дорогу только автомобилю",
      "Проедете первым"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_13_13",
    "ticket": "Билет 13 · Вопрос 13",
    "type": "crossroad_tram",
    "title": "В данной ситуации Вы не обязаны уступать дорогу трамваю при движении:",
    "explanation": "Перекресток регулируемый. Светофор с одноцветной сигнализацией, предназначенный для маршрутных ТС, разрешает движение прямо. Трамвай, поворачивающий направо, дожидается смены сигнала. Зеленый сигнал светофора разрешает Вам движение – проезжайте перекресток прямо первым.(Пункты 6.2, 6.8 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Прямо или направо",
      "Только прямо",
      "Только направо"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_13_14",
    "ticket": "Билет 13 · Вопрос 14",
    "type": "crossroad_traffic_light",
    "title": "Кто из водителей, выполняющих поворот, должен уступить дорогу пешеходам?",
    "explanation": "При повороте направо или налево при проезде перекрёстков, как регулируемых, так и нерегулируемых, водитель обязан уступить дорогу пешеходам, переходящим проезжую часть дороги, на которую он поворачивает. Оба водителя уступают дорогу пешеходам.(Пункт 13.1 ПДД)",
    "pddRule": "п. 13.1",
    "options": [
      "Только водитель легкового автомобиля",
      "Только водитель грузового автомобиля",
      "Оба"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_13_15",
    "ticket": "Билет 13 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Можете ли Вы в данной ситуации приступить к повороту налево?",
    "explanation": "Перекрёсток неравнозначный. Транспортные средства, находящиеся на главной дороге, имеют преимущество. Но так как Ваша траектория движения не пересекается с грузовиком, можете совершить движение через перекрёсток одновременно, при этом Вы должны учитывать преимущество грузовика, т.е. не создавать ему помех.(«Дорожные знаки», пункты 1.2 термин «Уступить дорогу», 13.9 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Можете",
      "Можете, только убедившись в том, что не создадите помех встречному автомобилю, выполняющему поворот налево",
      "Не можете"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_14_13",
    "ticket": "Билет 14 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "При включении зелёного сигнала светофора Вы должны уступить дорогу:",
    "explanation": "Правила предусматривают такую ситуацию. При включении разрешающего сигнала светофора водитель обязан уступить дорогу транспортным средствам, завершающим движение через перекрёсток.У Вас именно такая ситуация – уступаете дорогу всем автомобилям, находящимся в границах перекрестка, в данном случае – обоим автомобилям.(Пункт 13.8 ПДД)",
    "pddRule": "п. 13.8",
    "options": [
      "Только грузовому автомобилю, завершающему разворот на перекрёстке",
      "Только легковому автомобилю",
      "Обоим автомобилям"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_14_14",
    "ticket": "Билет 14 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток равнозначный. В равнозначных условиях трамваи имеют преимущество. В данной ситуации траектории движения трамваев не пересекаются, проезжают перекрёсток одновременно. Вы – после них.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только трамваю А",
      "Только трамваю Б",
      "Обоим трамваям"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_14_15",
    "ticket": "Билет 14 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "При повороте налево Вы:",
    "explanation": "Перекрёсток неравнозначный. Преимущество имеют транспортные средства, находящиеся на главной дороге. При повороте налево следует уступить дорогу транспортным средствам, движущимся прямо со встречного направления. Вы должны уступить только автобусу.(Пункты 13.9, 13.12 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Имеете преимущество",
      "Должны уступить дорогу только автобусу",
      "Должны уступить дорогу легковому автомобилю и автобусу"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_15_13",
    "ticket": "Билет 15 · Вопрос 13",
    "type": "crossroad_tram",
    "title": "В каком случае Вы обязаны пропустить трамвай?",
    "explanation": "Перекресток регулируется светофором, траектории движения трамвая и ваша пересекаются. Находясь в равнозначных условиях трамвай имеет преимущество перед безрельсовыми Т.С.Вы уступаете дорогу в обоих перечисленных случаях.(Пункты 6.2, 13.6 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "При повороте налево, перестроившись на трамвайные пути попутного направления",
      "При движении прямо",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_15_14",
    "ticket": "Билет 15 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "При движении в прямом направлении, Вам следует:",
    "explanation": "Перекрёсток равнозначный. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми транспортными средствами. Проезжает первым. Вы с водителем легкового автомобиля руководствуетесь «правилом правой руки». У Вас помехи справа нет. Проезжаете перекрёсток, уступая только трамваю.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу только трамваю",
      "Уступить дорогу трамваю и легковому автомобилю"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_15_15",
    "ticket": "Билет 15 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы должны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, между собой руководствуются «правилом правой руки». У Вас помеха справа, уступаете автобусу. Легковой автомобиль проедет последним, так как находится на второстепенной дороге.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_16_13",
    "ticket": "Билет 16 · Вопрос 13",
    "type": "crossroad_tram",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Кому вы должны уступить дорогу?",
    "explanation": "Перекрёсток регулируемый. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми транспортными средствами. Проезжает первым. Легковой автомобиль при повороте налево обязан уступить дорогу транспортным средствам, движущимся со встречного направления прямо и направо. Вы уступаете дорогу только трамваю.(Пункты 13.3, 13.4, 13.6 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Трамваю и автомобилю",
      "Только трамваю",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "type": "tram",
        "id": "tram_1",
        "name": "Трамвай",
        "side": "left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_16_14",
    "ticket": "Билет 16 · Вопрос 14",
    "type": "crossroad_priority_signs",
    "title": "При въезде на перекрёсток Вы:",
    "explanation": "При въезде на перекресток, на котором организовано круговое движение, обозначенный знаком 4.3 «Круговое движение», Вы обязаны уступить дорогу всем ТС, движущимся по такому перекрестку.(Пункт 13.11.1 ПДД)(Изменения ПДД от 8 ноября 2017)",
    "pddRule": "п. 13.11.1",
    "options": [
      "Должны уступить дорогу обоим транспортным средствам",
      "Должны уступить дорогу только автомобилю",
      "Имеете преимущество перед обоими транспортными средствами"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_16_15",
    "ticket": "Билет 16 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Преимущество имеют транспортные средства, находящиеся на главной дороге. Вы находитесь на второстепенной дороге и уступаете обоим транспортным средствам, независимо от направления их дальнейшего движения.(«Дорожные знаки», пункт 13.9 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только легковому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_17_13",
    "ticket": "Билет 17 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Обязаны ли Вы уступить дорогу автобусу?",
    "explanation": "«Правило правой руки» универсально. Оно не работает в двух случаях – один из случаев, когда ТС движется под дополнительную секцию, включенную одновременно с основным желтым или красным сигналом. В данной ситуации Вы обязаны уступить дорогу всем ТС, движущимся с других направлений. Вы обязаны уступить дорогу автобусу.(Пункт 13.5 ПДД)",
    "pddRule": "п. 13.5",
    "options": [
      "Обязаны",
      "Не обязаны"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_17_14",
    "ticket": "Билет 17 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. При «разводке» транспортных средств руководствуемся «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Первым проедет грузовик, движущийся прямо, после него грузовик с маячком оранжевого цвета (который не предоставляет «преимущество»), последним Вы.(«Дорожные знаки», пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Уступите дорогу обоим грузовым автомобилям",
      "Выехав на перекрёсток, уступите дорогу встречному грузовому автомобилю и завершите поворот",
      "Проедете перекресток первым"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_17_15",
    "ticket": "Билет 17 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "После въезда на этот перекресток:",
    "explanation": "После въезда на перекресток, на котором организовано круговое движение, обозначенный знаком 4.3 «Круговое движение», Вы будете иметь преимущество в движении перед легковым автомобилем, поскольку при въезде на этот перекресток его водитель обязан уступить дорогу ТС, движущимся по нему п. 13.11.1.(Изменения ПДД от 8 ноября 2017)",
    "pddRule": "п. 13.11.1",
    "options": [
      "Вы должны уступить дорогу легковому автомобилю, въезжающему на него",
      "Вы будете иметь преимущество перед легковым автомобилем, въезжающим на него",
      "Вам следует действовать по взаимной договоренности с водителем легкового автомобиля"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_18_13",
    "ticket": "Билет 18 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Обязаны ли Вы уступить дорогу легковому автомобилю при повороте направо?",
    "explanation": "Перекрёсток регулируемый. Знаки приоритета «не работают». При повороте налево водитель легкового автомобиля обязан уступить дорогу транспортным средствам, движущимся со встречного направления прямо или направо. У Вас преимущество.(Пункты 13.3, 13.4 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Обязаны",
      "Обязаны, если легковой автомобиль поворачивает налево",
      "Не обязаны"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_18_14",
    "ticket": "Билет 18 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены выполнить разворот. Ваши возможные действия?",
    "explanation": "Перекрёсток равнозначный. Водители ТС, траектории которых пересекаются в границах перекрестка, руководствуются «правилом правой руки».Правильный ответ – допускаются оба варианта действий.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Отказаться от преимущества в движении и приступить к развороту после проезда легкового автомобиля",
      "Выехать на перекресток первым и, уступив дорогу легковому автомобилю, закончить разворот",
      "Допускаются оба варианта действий"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_18_15",
    "ticket": "Билет 18 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. В данной ситуации:",
    "explanation": "Перекрёсток неравнозначный. Специальный жёлтый мигающий сигнал на грузовике преимуществ не предоставляет. Транспортные средства находятся на равнозначной дороге. При повороте налево водитель грузовика обязан уступить дорогу Вам, движущемуся прямо со встречного направления.Проезжаете перекресток первым.(«Дорожные знаки», пункты 3.4, 13.12 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Вы обязаны уступить дорогу грузовому автомобилю",
      "Вы имеете право проехать перекресток первым"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_19_13",
    "ticket": "Билет 19 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Ваши действия?",
    "explanation": "Перекрёсток регулируемый. Вы продолжаете движение под дополнительную секцию светофора, включенную одновременно с основным красным сигналом светофора без остановки у стоп-линии. Но в этом случае, продолжая движение, необходимо учитывать, что уступаете дорогу всем транспортным средствам, движущимся с других направлений. В случае создания помехи, Вы создадите опасную ситуацию, которая может перейти в аварийную, и тогда Вы станете виновником ДТП.(Пункты 13.3, 13.5 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Остановитесь перед стоп-линией",
      "Продолжите движение, уступая дорогу легковому автомобилю",
      "Продолжите движение, имея преимущество перед легковым автомобилем"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_19_14",
    "ticket": "Билет 19 · Вопрос 14",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте направо?",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Мотоциклист и легковой автомобиль имеют помеху справа. У Вас помехи нет, проедете перекрёсток первым, вторым - легковой автомобиль, мотоциклист - последним.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу только легковому автомобилю",
      "Уступить дорогу легковому автомобилю и мотоциклу"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_19_15",
    "ticket": "Билет 19 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Если невозможно определить наличие покрытия на дороге (темное время суток, грязь, снег и тому подобное), а знаков приоритета нет, то:",
    "explanation": "Если водитель не может определить наличие покрытия на дороге (темное время суток, грязь, снег и тому подобное), а знаков приоритета нет, он должен считать, что находится на второстепенной дороге(Дорожные знаки, пункт 13.13 ПДД)",
    "pddRule": "п. 13.13",
    "options": [
      "Вы имеете право считать, что находитесь на главной дороге",
      "Вам следует считать, что находитесь на равнозначной дороге",
      "Вы должны считать, что находитесь на второстепенной дороге"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_20_13",
    "ticket": "Билет 20 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток регулируемый. При повороте налево Вы обязаны уступить дорогу легковому автомобилю, движущемуся прямо со встречного направления, и пешеходам, переходящим проезжую часть дороги, на которую поворачиваете.(Пункты 13.1, 13.4 ПДД)",
    "pddRule": "п. 13.4",
    "options": [
      "Только встречному автомобилю",
      "Только пешеходам",
      "Встречному автомобилю и пешеходам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "clear_crossroad",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "red"
    },
    "signs": []
  },
  {
    "id": "ticket_20_14",
    "ticket": "Билет 20 · Вопрос 14",
    "type": "crossroad",
    "title": "При повороте направо Вам следует:",
    "explanation": "Перекрёсток равнозначный. При определении порядка проезда перекрёстка водители руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. У Вас помеха справа отсутствует, проезжаете перекрёсток первым.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Уступить дорогу легковому автомобилю",
      "Проехать перекрёсток первым"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Встречный автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Встречный автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_20_15",
    "ticket": "Билет 20 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, между собой руководствуются «правилом правой руки». После их проезда этим же правилом пользуются транспортные средства, находящиеся на второстепенной дороге. Первым проезжает мотоциклист, вторым – автобус, далее легковой автомобиль. Вы последним, уступив всем транспортным средствам.(«Дорожные знаки», пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Автобусу и мотоциклу",
      "Легковому автомобилю и автобусу",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "type": "car",
        "id": "npc_car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_21_13",
    "ticket": "Билет 21 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Кому Вы должны уступить дорогу при повороте налево.",
    "explanation": "Перекрёсток регулируемый. Знаки приоритета «не работают». Первым на красный сигнал светофора выезжает на перекрёсток «оперативник» (от сигналов светофора он имеет право отступать) с включенными проблесковым маячком и специальным звуковым сигналом, которому остальные обязаны обеспечить беспрепятственный проезд. При повороте налево Вы уступаете дорогу мотоциклисту, движущемуся прямо со стороны встречного направления. Проезжаете перекрёсток последним, уступая обоим транспортным средствам.(Пункты 3.1, 3.2, 13.3, 13.4 ПДД)",
    "pddRule": "п. 3.1",
    "options": [
      "Только мотоциклу",
      "Только автомобилю с включенными проблесковым маячком и специальным звуковым сигналом",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Спецмашина",
        "color": "#0574F8"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_special",
        "type": "special",
        "name": "Спецмашина",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8",
        "beacon": "blue",
        "siren": true
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_21_14",
    "ticket": "Билет 21 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. Водители между собой руководствуются «правилом правой руки». У Вас помеха справа. У мотоциклиста тоже. Отсутствует помеха справа у водителя легкового автомобиля, траектория движения которого не пересекается с Вашей. Он проезжает первым, мотоциклист – вторым, Вы – последним.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекрёсток первым",
      "Проедете перекресток одновременно со встречным автомобилем до проезда мотоцикла",
      "Проедете перекрёсток последним"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "turn_right",
        "color": "#2BC280"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_21_15",
    "ticket": "Билет 21 · Вопрос 15",
    "type": "crossroad",
    "title": "Как Вам следует поступить при движении в прямом направлении?",
    "explanation": "В прямом направлении дорога с твердым покрытием. Грузовик будет выезжать на перекресток с грунтовой дороги, которая в данной ситуации является второстепенной. Перекресток неравнозначный. Вы двигаетесь на главной дороге, поэтому проезжаете перекресток первым.(Пункты 1.2 термин «Главная дорога», 13.9 ПДД)",
    "pddRule": "п. 1.2",
    "options": [
      "Уступить дорогу грузовому автомобилю, выезжающему с грунтовой дороги",
      "Проехать перекресток первым"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_22_13",
    "ticket": "Билет 22 · Вопрос 13",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Зеленый сигнал светофора дает вам право двигаться налево п. 6.2. При этом вы должны выехать в намеченном направлении независимо от сигнала светофора на выезде с перекрестка п. 13.7.",
    "pddRule": "",
    "options": [
      "Выполните маневр без остановки на перекрестке",
      "Повернете налево и остановитесь в разрыве разделительной полосы, дождетесь зеленого сигнала светофора на выезде с перекрестка и завершите маневр",
      "Остановитесь перед перекрестком, дождетесь зеленого сигнала светофора на выезде с перекрестка и начнете выполнение маневра"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_22_14",
    "ticket": "Билет 22 · Вопрос 14",
    "type": "crossroad",
    "title": "В каком случае Вы должны уступить дорогу трамваю?",
    "explanation": "Перекрёсток равнозначный. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми транспортными средствами. Вы уступаете дорогу в обоих перечисленных случаях.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "При повороте налево",
      "При движении прямо",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_22_15",
    "ticket": "Билет 22 · Вопрос 15",
    "type": "crossroad",
    "title": "Вы намерены повернуть направо. Можете ли Вы приступить к повороту?",
    "explanation": "При повороте направо Вы должны двигаться по возможности ближе к правому краю проезжей части, т.е. по крайней правой полосе, которая свободна. Если Вы убеждены, что не создадите помеху находящемуся на главной дороге и имеющему преимущество грузовому автомобилю, выезжаете на перекрёсток, не дожидаясь его проезда через перекрёсток, так как знак 2.4 «Уступите дорогу» не предписывает совершать обязательную остановку перед пересечением.(Пункты 1.2 термин «Уступить дорогу», 13.9 ПДД, «Дорожные знаки»)",
    "pddRule": "п. 1.2",
    "options": [
      "Можете",
      "Можете, когда убедитесь, что при этом не будут созданы помехи грузовому автомобилю",
      "Не можете"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_23_13",
    "ticket": "Билет 23 · Вопрос 13",
    "type": "crossroad",
    "title": "Как следует поступить в этой ситуации, если Вам необходимо повернуть направо?",
    "explanation": "Правая рука регулировщика вытянута вперед. Со стороны левого бока безрельсовым транспортным средствам разрешено движение во всех направлениях – прямо, направо, налево и разворот. При повороте направо Вы обязаны уступить дорогу пешеходам, переходящим проезжую часть, на которую поворачиваете.(Пункты 6.10, 13.1 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Остановиться и дождаться другого сигнала регулировщика",
      "Повернуть направо, уступив дорогу пешеходам",
      "Повернуть направо, имея преимущество в движении перед пешеходами"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_23_14",
    "ticket": "Билет 23 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. В данной ситуации:",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки», т.е. у кого помеха справа тот и уступает. Постоянно контролируя отсутствие помехи справа, проезжаете перекрёсток первым.(Пункты 13.11, 13.12 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Вы обязаны уступить дорогу легковому автомобилю",
      "Вы имеете право проехать перекресток первым"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_23_15",
    "ticket": "Билет 23 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, между собой руководствуются «правилом правой руки». У Вас помеха справа – уступаете автобусу.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Обоим транспортным средствам",
      "Только автобусу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "cross_right",
        "targetAction": "turn_left",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_24_13",
    "ticket": "Билет 24 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "При повороте налево Вы:",
    "explanation": "Перекрёсток регулируемый. Всем трем ТС разрешено движение. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми ТС. Он проезжает первым. Вы - при повороте налево обязаны уступить автомобилю, движущемуся навстречу прямо.Правильный ответ – должны уступить дорогу обоим транспортным средствам.(Пункты 6.2, 13.4, 13.6 ПДД)",
    "pddRule": "п. 6.2",
    "options": [
      "Должны уступить дорогу обоим транспортным средствам",
      "Должны уступить дорогу только легковому автомобилю",
      "Имеете право проехать перекресток первым"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_1",
        "type": "tram",
        "name": "Трамвай",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_24_14",
    "ticket": "Билет 24 · Вопрос 14",
    "type": "crossroad",
    "title": "Кто имеет право проехать перекресток первым, если все намерены двигаться прямо?",
    "explanation": "Перекрёсток равнозначный. Мигающий маячок жёлтого цвета водителю грузовика преимущества не предоставляет (пункт 3.4 ПДД). «Правило правой руки» не применить, так как у всех помеха справа. Действительно, объяснения такой ситуации в Правилах нет. Водителям следует по договорённости обеспечить беспрепятственный проезд только одного транспортного средства, а далее начнёт действовать «правило правой руки».",
    "pddRule": "п. 3.4",
    "options": [
      "Водитель троллейбуса",
      "Вы вместе с водителем троллейбуса",
      "В данной ситуации очередность проезда определяется по взаимной договоренности водителей"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_24_15",
    "ticket": "Билет 24 · Вопрос 15",
    "type": "crossroad",
    "title": "В каком случае Вы обязаны уступить дорогу пешеходам?",
    "explanation": "При проезде любых перекрёстков с поворотом налево или направо водитель обязан уступить дорогу пешеходам, переходящим проезжую часть дороги, на которую он поворачивает.(Пункт 13.1 ПДД)",
    "pddRule": "п. 13.1",
    "options": [
      "Только при повороте налево",
      "Только при повороте направо",
      "В обоих случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_25_13",
    "ticket": "Билет 25 · Вопрос 13",
    "type": "crossroad",
    "title": "Значения каких дорожных знаков отменяются сигналами светофора?",
    "explanation": "Движение регулируется: регулировщиком, сигналами светофора, знаками приоритета, разметкой, дорожным покрытием, «правилом правой руки». По вышеперечисленному «принципу приоритетности регулирования дорожного движения» знаки приоритета работают (т.е. ими мы руководствуемся) в том случае, когда отсутствует регулировщик, светофор выключен, неисправен, переведён в «жёлтый мигающий режим».(«Дорожные знаки», пункты 6.15 и 13.3 ПДД)",
    "pddRule": "п. 6.15",
    "options": [
      "Знаков приоритета",
      "Запрещающих знаков",
      "Предписывающих знаков",
      "Всех перечисленных знаков"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_25_14",
    "ticket": "Билет 25 · Вопрос 14",
    "type": "crossroad",
    "title": "При повороте направо Вы должны уступить дорогу:",
    "explanation": "При повороте направо или налево водитель обязан уступить дорогу пешеходам, лицам, использующим для передвижения СИМ и велосипедистам, пересекающим проезжую часть дороги, на которую он поворачивает.Это правило проезда перекрестков касается как регулируемых, так и нерегулируемых перекрестков.(Пункт 13.1 ПДД)",
    "pddRule": "п. 13.1",
    "options": [
      "Только велосипедисту",
      "Только пешеходам",
      "Пешеходам и велосипедисту"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы направо",
        "color": "#ED4621"
      },
      {
        "label": "Велосипедист",
        "color": "#2BC280"
      },
      {
        "label": "Пешеход",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "id": "cyclist",
        "type": "cyclist",
        "name": "Велосипедист",
        "side": "cross_right_edge",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "pedestrian",
        "type": "pedestrian",
        "name": "Пешеход",
        "side": "crosswalk_right",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_25_15",
    "ticket": "Билет 25 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены повернуть налево. Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток неравнозначный. Транспортные средства, находящиеся на главной дороге, имеют преимущество. Между собой руководствуются «правилом правой руки». После их проезда, руководствуясь тем же правилом, проедут транспортные средства, находящиеся на второстепенной дороге. Первым проезжает перекрёсток легковой автомобиль, Вы – вторым, мотоциклист – третьим, автобус – последним.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Никому",
      "Только легковому автомобилю",
      "Легковому автомобилю и автобусу",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_26_13",
    "ticket": "Билет 26 · Вопрос 13",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "В обычной ситуации водитель выезжает с перекрёстка независимо от сигналов светофора на выходе с перекрёстка. Но здесь ситуация иная. Применено раздельное действие светофоров.На перекрёстке два пересечения проезжих частей. Повернув налево, Вы обязаны при запрещающем сигнале светофора остановиться у «стоп-линии» (разметки 1.12). После включения разрешающего сигнала продолжаете движение через перекрёсток.(Пункт 13.7 ПДД)",
    "pddRule": "п. 13.7",
    "options": [
      "Остановитесь перед перекрестком, дождетесь зеленого сигнала светофора, установленного на разделительной полосе, и начнете выполнение маневра",
      "Выехав на перекрёсток, остановитесь у стоп-линии и, дождавшись зелёного сигнала светофора, установленного на разделительной полосе, завершите маневр",
      "Выполните маневр без остановки на перекрестке"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_26_14",
    "ticket": "Билет 26 · Вопрос 14",
    "type": "crossroad",
    "title": "Кому Вы должны уступить дорогу при повороте налево ?",
    "explanation": "Перекрёсток равнозначный. При любой его конфигурации водители руководствуются «правилом правой руки». Первым проезжает грузовик, так как у него нет помехи справа, вторым легковой автомобиль, Вы – последним.Вам следует уступить обоим транспортным средствам.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только легковому автомобилю",
      "Только грузовому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_26_15",
    "ticket": "Билет 26 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "При движении прямо Вы обязаны уступить дорогу:",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге. После их проезда проезжают транспортные средства, находящиеся на второстепенной дороге, которые между собой руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Помеха справа у мотоциклиста, он уступает Вам. Транспортные средства проедут перекрёсток в следующем порядке: автобус, легковой автомобиль, Вы, мотоциклист.(«Дорожные знаки», пункты 13.9, 13.10 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только легковому автомобилю",
      "Автобусу и легковому автомобилю",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_27_13",
    "ticket": "Билет 27 · Вопрос 13",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте направо?",
    "explanation": "Перекрёсток регулируемый. Со стороны левого бока при таком жесте регулировщика безрельсовым транспортным средствам движение разрешается во всех направлениях. Трамваи двигаются только «по направлению рук регулировщика». В данной ситуации трамвай продолжать движение не может. Его водитель будет дожидаться смены сигнала регулировщика. Вы продолжаете движение через перекрёсток, т.е. проезжаете его первым.(Пункт 6.10 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Остановиться и дождаться другого сигнала регулировщика",
      "Проехать перекресток, уступив дорогу трамваю",
      "Проехать перекресток первым"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_27_14",
    "ticket": "Билет 27 · Вопрос 14",
    "type": "crossroad",
    "title": "Как Вам следует поступить, двигаясь по перекрестку с круговым движением?",
    "explanation": "При въезде по дороге, не являющейся главной, на перекресток, на котором организовано круговое движение и который обозначен знаком 4.3, водитель транспортного средства обязан уступить дорогу транспортным средствам, движущимся по такому перекрестку. (Третий исключительный случай, когда «правило правой руки» не работает).В данной ситуации Вы имеете преимущество и проезжаете перекресток первым.При въезде на перекресток водитель грузового автомобиля обязан уступить дорогу ВСЕМ ТС, движущимся по такому перекрестку.(Пункт 13.11.1 ПДД)",
    "pddRule": "п. 13.11.1",
    "options": [
      "Уступить дорогу грузовому автомобилю",
      "Проехать перекресток первым",
      "Действовать по взаимной договоренности с водителем грузового автомобиля"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_27_15",
    "ticket": "Билет 27 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге. После их проезда проезжают транспортные средства, находящиеся на второстепенной дороге, которые между собой руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Помеха справа у мотоциклиста, он уступает Вам. Транспортные средства проедут перекрёсток в следующем порядке: автобус, легковой автомобиль, Вы, мотоциклист.(«Дорожные знаки», пункты 13.9, 13.10 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только легковому автомобилю",
      "Легковому автомобилю и автобусу",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_28_13",
    "ticket": "Билет 28 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток регулируемый. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми транспортными средствами. Вместе с ним одновременно, так как траектории движения не пересекаются, проедет легковой автомобиль, поворачивающий направо, которому Вы при повороте налево обязаны также уступить. Вы проедете перекрёсток последним.(Пункты 13.3, 13.4, 13.6 ПДД)",
    "pddRule": "п. 13.3",
    "options": [
      "Только автомобилю",
      "Только трамваю",
      "Автомобилю и трамваю",
      "Никому"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_1",
        "type": "tram",
        "name": "Трамвай",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#0574F8",
        "position": [
          -0.6,
          0,
          13
        ],
        "rotationY": 3.141592653589793
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "turn_right",
        "color": "#2BC280",
        "position": [
          -3.6,
          0,
          10.5
        ],
        "rotationY": 3.141592653589793
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_28_14",
    "ticket": "Билет 28 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы должны уступить дорогу грузовому автомобилю:",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки». У Вас помеха справа будет только при движении прямо - Вы уступаете дорогу грузовому автомобилю. При повороте направо помеха справа отсутствует.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только при движении прямо",
      "Только при повороте направо",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_28_15",
    "ticket": "Билет 28 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены развернуться. Кому Вам необходимо уступить дорогу?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество перед остальными независимо от их дальнейшего направления движения. Между собой руководствуются «правилом правой руки». Грузовик проезжает первым, Вы после него, легковой автомобиль - последним.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только грузовому автомобилю",
      "Только легковому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы на разворот",
        "color": "#ED4621"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_29_13",
    "ticket": "Билет 29 · Вопрос 13",
    "type": "crossroad",
    "title": "При выполнении какого маневра водитель легкового автомобиля имеет преимущество в движении?",
    "explanation": "Водитель легкового автомобиля, движущийся под включенную зеленую стрелку в дополнительной секции, включенную одновременно с основным зеленым сигналом, может повернуть налево и совершить разворот. При этом движущиеся под включенную зеленую стрелку, в дополнительной секции, включенную одновременно с основным красным сигналом, автобус и грузовой автомобиль обязаны уступить всем другим Т.С, движущимся со всех других направлений. Водитель легкового автомобиля имеет преимущество в данной ситуации при выполнении любого маневра из перечисленных.(Пункт 13.5 ПДД)",
    "pddRule": "п. 13.5",
    "options": [
      "Только при повороте налево",
      "Только при развороте",
      "При выполнении любого маневра из перечисленных"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_29_14",
    "ticket": "Билет 29 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Вы и трамвай находитесь в равнозначных условиях. Трамвай в таком случае имеет преимущество перед безрельсовыми транспортными средствами. Уступаете дорогу трамваю.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Уступите дорогу трамваю, выполнив поворот с левой полосы",
      "Пропустите трамвай, перестроитесь на трамвайные пути попутного направления, после чего выполните поворот",
      "Проедете перекресток первым"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_29_15",
    "ticket": "Билет 29 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при движении в прямом направлении?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге. Между собой они руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. Вы находитесь на второстепенной дороге - уступаете обоим транспортным средствам.(«Дорожные знаки» 2.4, 8.13, пункты 13.9, 13.10 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только легковому автомобилю",
      "Только автобусу",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_30_13",
    "ticket": "Билет 30 · Вопрос 13",
    "type": "crossroad",
    "title": "В каком случае Вы обязаны уступить дорогу грузовому автомобилю?",
    "explanation": "Перекрёсток регулируемый. Вам разрешено движение. При повороте налево, развороте следует уступить дорогу транспортным средствам, движущимся со встречного направления прямо и направо. Уступаете грузовику в обоих перечисленных случаях.(Пункты 13.3, 13.4 ПДД)",
    "pddRule": "п. 13.3",
    "options": [
      "При повороте налево",
      "При развороте",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_30_14",
    "ticket": "Билет 30 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены продолжить движение прямо при желтом мигающем сигнале светофора. Ваши действия?",
    "explanation": "Перекрёсток при жёлтом мигающем светофоре является нерегулируемым, в данном случае равнозначным, так как знаков приоритета нет. Руководствуемся «правилом правой руки», т.е. у кого помеха справа, тот и уступает. У Вас помеха справа – проедете перекрёсток последним, уступив дорогу гужевой повозке.(Пункты 13.3, 13.11 ПДД)",
    "pddRule": "п. 13.3",
    "options": [
      "Остановитесь и продолжите движение только после включения зеленого сигнала светофора",
      "Уступите дорогу гужевой повозке",
      "Проедете перекресток первым вместе со встречным автомобилем"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_30_15",
    "ticket": "Билет 30 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены повернуть налево. Кому Вы обязаны уступить дорогу?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге, имеют преимущество, между собой руководствуются «правилом правой руки». После их проезда, руководствуясь этим же правилом, проедут транспортные средства, находящиеся на второстепенной дороге. Вы проезжаете первым, никому не уступая. Мотоциклист – вторым, автобус – третьим, легковой автомобиль – последним.(Пункты 13.9, 13.1, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Легковому автомобилю и автобусу",
      "Только автобусу",
      "Только мотоциклу",
      "Никому"
    ],
    "correctAnswerIndex": 3,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "turn_right",
        "color": "#2BC280"
      },
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_31_13",
    "ticket": "Билет 31 · Вопрос 13",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток регулируемый. У регулировщика руки опущены. Движение со стороны правого и левого бока безрельсовым транспортным средствам разрешается прямо и направо. Вы же намереваетесь повернуть налево. Поэтому Вам необходимо остановиться перед стоп-линией и дождаться соответствующего Вашему намерению сигнала регулировщика, после чего выполнить маневр.(Пункты 6.10, 6.13, 13.3 ПДД, «Горизонтальная разметка» 1.12)",
    "pddRule": "п. 6.10",
    "options": [
      "Остановиться у стоп-линии и дождаться сигнала регулировщика, разрешающего поворот",
      "Выехав на перекресток, остановиться и дождаться сигнала регулировщика, разрешающего поворот",
      "Повернуть, уступив дорогу встречному автомобилю"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_31_14",
    "ticket": "Билет 31 · Вопрос 14",
    "type": "crossroad_tram",
    "title": "Вы намерены проехать перекрёсток в прямом направлении. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. Трамвай на равнозначных перекрёстках имеет преимущество перед безрельсовыми транспортными средствами независимо от его дальнейшего направления движения. Безрельсовые транспортные средства руководствуются между собой «правилом правой руки», т.е. у кого помеха справа, тот и уступает дорогу. У Вас помеха справа – уступаете дорогу грузовику.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекресток вместе с трамваем, не уступая дорогу грузовому автомобилю",
      "Проедете перекресток, уступив дорогу грузовому автомобилю"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_1",
        "type": "tram",
        "name": "Трамвай",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_31_15",
    "ticket": "Билет 31 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при движении прямо?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Транспортные средства, находящиеся на главной дороге имеют преимущество, между собой руководствуются «правилом правой руки». После них, руководствуясь этим же правилом, проезжают перекрёсток транспортные средства, находящиеся на второстепенной дороге. Первым проедет мотоциклист, вторым – автобус, третьим – легковой автомобиль. Вы последним, уступив всем транспортным средствам.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только мотоциклу",
      "Мотоциклу и легковому автомобилю",
      "Автобусу и мотоциклу",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 3,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      },
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "turn_left",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "west"
        ]
      }
    ]
  },
  {
    "id": "ticket_32_13",
    "ticket": "Билет 32 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток регулируемый. Знаки приоритета «не работают». Грузовик с «жёлтой мигалкой» стоит и дожидается разрешающего ему движение сигнала светофора, так как отступать от требований сигналов светофора жёлтый специальный сигнал не разрешает. Вы при повороте налево обязаны уступить дорогу транспортным средствам, движущимся прямо со встречного направления. Уступаете дорогу автобусу.(Пункты 3.4, 13.3, 13.4 ПДД)",
    "pddRule": "п. 3.4",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу только грузовому автомобилю с включенным проблесковым маячком",
      "Уступить дорогу только автобусу"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C",
        "beacon": "amber"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_32_14",
    "ticket": "Билет 32 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены развернуться. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. При определении порядка проезда перекрёстка водители руководствуются «правилом правой руки». Во время разворота у Вас будет помеха справа, уступаете дорогу.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Развернётесь первым",
      "Выедете на перекрёсток и, уступив дорогу легковому автомобилю, завершите разворот",
      "Будете действовать по взаимной договоренности с водителем легкового автомобиля"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_32_15",
    "ticket": "Билет 32 · Вопрос 15",
    "type": "crossroad",
    "title": "Кому Вы обязаны уступить дорогу при движении прямо?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге, при этом безрельсовые транспортные средства между собой руководствуются «правилом правой руки», уступая трамваю, находящемуся с ними в равнозначных условиях. Вы уступаете дорогу трамваю и легковому автомобилю, которые проедут перекрёсток одновременно, так как их траектории движения не пересекаются. Мотоциклист уступает всем, потому что находится на второстепенной дороге.(«Дорожные знаки», пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только трамваю",
      "Только легковому автомобилю",
      "Трамваю и легковому автомобилю",
      "Всем транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_33_13",
    "ticket": "Билет 33 · Вопрос 13",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте направо?",
    "explanation": "Для поворота направо Вы должны пересечь трамвайные пути. Оба трамвая так же, как и Вы, имеют право на движение, они двигаются «по рукам регулировщика». Вы им уступаете, так как при одновременном праве на движение трамвай имеет преимущество перед безрельсовыми транспортными средствами.(Пункты 6.10, 13.6 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Проехать перекресток первым",
      "Уступить дорогу только трамваю А",
      "Уступить дорогу только трамваю Б",
      "Уступить дорогу обоим трамваям"
    ],
    "correctAnswerIndex": 3,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_33_14",
    "ticket": "Билет 33 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. Водители между собой руководствуются «правилом правой руки». Первым начинаете движение Вы, поскольку в первоначальный момент не имеете помехи справа. Выкатившись на перекрёсток, перед самым поворотом налево останавливаетесь, так как справа от Вас по траектории движения находится мотоцикл. После того, как мотоцикл проедет, Вы можете завершить маневр. Легковое ТС проедет перекресток последним.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекрёсток первым",
      "Выедете на перекресток первым и, уступив дорогу мотоциклу, завершите поворот",
      "Уступите дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_33_15",
    "ticket": "Билет 33 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы обязаны уступить дорогу при движении прямо:",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге, которые между собой руководствуются «правилом правой руки». Вы находитесь на второстепенной дороге, уступаете дорогу обоим транспортным средствам.(«Дорожные знаки» 2.4, 8.13; пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Только легковому автомобилю",
      "Только грузовому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_34_13",
    "ticket": "Билет 34 · Вопрос 13",
    "type": "crossroad",
    "title": "Как Вам следует поступить при движении в прямом направлении?",
    "explanation": "Перекрёсток регулируемый. Трамваи двигаются только «по направлению рук регулировщика», т.е. прямо. Водителю трамвая поворот направо запрещён. Соответственно он стоит и дожидается смены сигнала регулировщика. Вам можно продолжить движение прямо или направо. Проезжаете перекрёсток первым.(Пункт 6.10 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Проехать перекрёсток первым",
      "Уступить дорогу трамваю",
      "Дождаться другого сигнала регулировщика"
    ],
    "correctAnswerIndex": 0,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_34_14",
    "ticket": "Билет 34 · Вопрос 14",
    "type": "crossroad",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки». У вас помехой справа является только автомобиль, поэтому вы обязаны ему уступить дорогу.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только мотоциклу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_34_15",
    "ticket": "Билет 34 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Вы намерены повернуть налево. Ваши действия?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Преимущество имеют транспортные средства, находящиеся на главной дороге, которые между собой руководствуются «правилом правой руки». После их проезда, проезжают транспортные средства, находящиеся на второстепенной дороге. Вы находитесь на второстепенной дороге. Уступаете обоим транспортным средствам.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Уступите дорогу обоим транспортным средствам",
      "Уступите дорогу только легковому автомобилю",
      "Уступите дорогу только автобусу"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "cross_left",
        "targetAction": "turn_right",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "north",
          "west"
        ]
      }
    ]
  },
  {
    "id": "ticket_35_13",
    "ticket": "Билет 35 · Вопрос 13",
    "type": "crossroad",
    "title": "Вам необходимо уступить дорогу другим участникам движения:",
    "explanation": "При повороте направо Вы обязаны уступить дорогу пешеходам. При повороте налево или развороте – трамваю, имеющему преимущество в равнозначных условиях. Никаких помех нет при движении прямо.Правильный ответ - в обоих перечисленных случаях.(Пункты 6.2, 13.1, 13.6 ПДД)",
    "pddRule": "п. 6.2",
    "options": [
      "Только при повороте налево или развороте",
      "Только при повороте направо",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_35_14",
    "ticket": "Билет 35 · Вопрос 14",
    "type": "crossroad",
    "title": "Вы намерены продолжить движение прямо. Ваши действия?",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает. У Вас помеха справа, грузовик имеет преимущество.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекресток первым",
      "Уступите дорогу грузовому автомобилю, так как он приближается справа",
      "Уступите дорогу грузовому автомобилю, так как он находится на главной дороге"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_35_15",
    "ticket": "Билет 35 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Бесспорно преимущество имеет «оперативник» с мигалкой синего цвета и включенной сиреной. Все остальные обязаны обеспечить ему беспрепятственный проезд перекрёстка. После его проезда проезжаете Вы, так как находитесь на главной дороге и имеете преимущество перед грузовиком, находящимся на второстепенной дороге.(Пункты 3.1, 13.9 ПДД)",
    "pddRule": "п. 3.1",
    "options": [
      "Обоим транспортным средствам",
      "Автомобилю с включенными проблесковым маячком и специальным звуковым сигналом",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Спецмашина",
        "color": "#0574F8"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_special",
        "type": "special",
        "name": "Спецмашина",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#0574F8",
        "beacon": "blue",
        "siren": true
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "west"
        ]
      }
    ]
  },
  {
    "id": "ticket_36_13",
    "ticket": "Билет 36 · Вопрос 13",
    "type": "crossroad",
    "title": "Вы намерены повернуть направо. Ваши действия?",
    "explanation": "Со стороны вытянутой правой руки регулировщика безрельсовым транспортным средствам движение разрешается только направо. При этом разворачивающийся автомобиль, руководствуясь «правилом правой руки», уступает Вам дорогу.(Пункт 6.10 ПДД)",
    "pddRule": "п. 6.10",
    "options": [
      "Дождетесь другого сигнала регулировщика",
      "Уступите дорогу легковому автомобилю, осуществляющему разворот",
      "Проедете перекресток первым"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_36_14",
    "ticket": "Билет 36 · Вопрос 14",
    "type": "crossroad",
    "title": "В каком случае Вы должны пропустить трамвай?",
    "explanation": "Вы и трамвай находитесь на одной дороге в равнозначных условиях. В таком случае трамвай всегда имеет преимущество перед безрельсовыми транспортными средствами. Вы должны уступить дорогу трамваю в обоих перечисленных случаях.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "При повороте налево, перестроившись на трамвайные пути попутного направления",
      "При движении прямо",
      "В обоих перечисленных случаях"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_36_15",
    "ticket": "Билет 36 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток нерегулируемый, неравнозначный. Преимущество имеют транспортные средства, находящиеся на главной дороге, которые между собой руководствуются «правилом правой руки». После проезжают перекрёсток транспортные средства, находящиеся на второстепенной дороге. Первым проезжает грузовик, Вы ему уступаете. Последним проедет легковой автомобиль.(Пункты 13.3, 13.9, 13.12 ПДД)",
    "pddRule": "п. 13.3",
    "options": [
      "Уступить дорогу обоим транспортным средствам",
      "Уступить дорогу только грузовому автомобилю",
      "Проехать перекресток первым"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_37_13",
    "ticket": "Билет 37 · Вопрос 13",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте направо?",
    "explanation": "При повороте направо, налево на любом перекрёстке (регулируемом, нерегулируемом) водитель обязан уступить дорогу пешеходам, переходящим проезжую часть дороги, на которую он поворачивает.(Пункты 6.2, 13.1 ПДД)",
    "pddRule": "п. 6.2",
    "options": [
      "Остановиться перед стоп-линией и, пропустив пешеходов, повернуть направо",
      "Выехав на перекрёсток, остановиться перед пешеходным переходом, чтобы пропустить пешеходов",
      "Продолжить движение без остановки на перекрёстке"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_37_14",
    "ticket": "Билет 37 · Вопрос 14",
    "type": "crossroad",
    "title": "При движении в каком направлении Вы будете иметь преимущество?",
    "explanation": "Перекрёсток равнозначный. Водители руководствуются «правилом правой руки». У Вас помехи справа нет, в любом направлении из перечисленных. Проезжаете перекрёсток первым.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только при повороте направо",
      "Только при повороте налево",
      "В любом направлении из перечисленных"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_37_15",
    "ticket": "Билет 37 · Вопрос 15",
    "type": "crossroad_tram",
    "title": "Вы намерены продолжить движение прямо. Ваши действия:",
    "explanation": "Перекрёсток неравнозначный. Вы и трамвай находитесь на главной дороге. «Правило правой руки» в этом случае не работает. Трамвай в равнозначных условиях имеет преимущество перед безрельсовыми транспортными средствами. Уступаете дорогу трамваю.(Пункт 13.11 ПДД, «Дорожные знаки»)",
    "pddRule": "п. 13.11",
    "options": [
      "Проедете перекрёсток первым",
      "Уступите дорогу трамваю"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_1",
        "type": "tram",
        "name": "Трамвай",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#0574F8"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_38_13",
    "ticket": "Билет 38 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток регулируемый. Знаки приоритета «не работают». «Оперативник» со специальными сигналами отступает от требований сигналов светофора. Другие водители обязаны обеспечить его беспрепятственный проезд. При повороте налево Вы обязаны уступить легковому автомобилю, движущемуся прямо со встречного направления.(Пункты 3.1, 3.2, 13.3, 13.4 ПДД)",
    "pddRule": "п. 3.1",
    "options": [
      "Проехать перекресток первым",
      "Уступить дорогу только автомобилю с включенными проблесковым маячком и специальным звуковым сигналом",
      "Уступить дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Спецмашина",
        "color": "#0574F8"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_special",
        "type": "special",
        "name": "Спецмашина",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#0574F8",
        "beacon": "blue",
        "siren": true
      },
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_38_14",
    "ticket": "Билет 38 · Вопрос 14",
    "type": "crossroad",
    "title": "При движении в каком направлении Вы обязаны уступить дорогу трамваю?",
    "explanation": "Перекрёсток равнозначный. Вы и трамвай находитесь в равнозначных условиях. В таком случае трамвай всегда имеет преимущество перед безрельсовыми транспортными средствами.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Только налево",
      "Только прямо",
      "В обоих перечисленных"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_38_15",
    "ticket": "Билет 38 · Вопрос 15",
    "type": "crossroad",
    "title": "Вы намерены повернуть направо. Можете ли Вы приступить к повороту?",
    "explanation": "Перекрёсток неравнозначный. Знак 2.4 обязывает Вас уступить дорогу транспортным средствам, движущимся по пересекаемой дороге. Только после того как убедитесь, что грузовой автомобиль действительно поворачивает налево и Ваше движение не может создать ему помеху, выезжаете на перекрёсток, чтобы совершить поворот направо.(Пункты 1.2, 13.9 ПДД, «Дорожные знаки»)",
    "pddRule": "п. 1.2",
    "options": [
      "Можете",
      "Можете после того, как грузовой автомобиль начнет выполнять поворот налево",
      "Не можете"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_39_13",
    "ticket": "Билет 39 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены проехать перекресток в прямом направлении. Ваши действия?",
    "explanation": "Перекресток регулируется светофором. Знаки приоритета «не работают». Вы и трамвай находитесь в равнозначных условиях. Трамвай в таких ситуациях всегда имеет преимущество перед безрельсовыми ТС, поэтому Вы уступаете дорогу трамваю.(Пункт 13.6 ПДД)",
    "pddRule": "п. 13.6",
    "options": [
      "Проедете первым, руководствуясь сигналом светофора",
      "Проедете первым, руководствуясь знаком «Главная дорога»",
      "Уступите дорогу трамваю"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_1",
        "type": "tram",
        "name": "Трамвай",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#0574F8"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      }
    ]
  },
  {
    "id": "ticket_39_14",
    "ticket": "Билет 39 · Вопрос 14",
    "type": "crossroad",
    "title": "Как Вам следует поступить при повороте налево?",
    "explanation": "Перекрёсток равнозначный. Водители безрельсовых транспортных средств между собой руководствуются «правилом правой руки», т.е. у кого помеха справа, тот и уступает дорогу. У Вас помеха справа, легковой автомобиль проезжает первым.(Пункт 13.11 ПДД)",
    "pddRule": "п. 13.11",
    "options": [
      "Уступить дорогу легковому автомобилю",
      "Проехать перекресток первым"
    ],
    "correctAnswerIndex": 0,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_39_15",
    "ticket": "Билет 39 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы должны уступить дорогу при движении прямо?",
    "explanation": "Перекрёсток неравнозначный. Главная дорога меняет направление. Первоначально проезжают перекрёсток транспортные средства, находящиеся на главной дороге. Они имеют преимущество. Между собой они руководствуются «правилом правой руки». У Вас помеха справа, уступаете только легковому автомобилю.(Пункты 13.9, 13.10, 13.11 ПДД)",
    "pddRule": "п. 13.9",
    "options": [
      "Легковому автомобилю и мотоциклу",
      "Только легковому автомобилю",
      "Никому"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Автомобиль",
        "color": "#2BC280"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_car",
        "type": "car",
        "name": "Автомобиль",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#2BC280"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "opposite",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#8B5CF6"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.1",
        "name": "Главная дорога"
      },
      {
        "code": "8.13",
        "name": "Направление главной дороги",
        "mainRoad": [
          "south",
          "east"
        ]
      }
    ]
  },
  {
    "id": "ticket_40_13",
    "ticket": "Билет 40 · Вопрос 13",
    "type": "crossroad_traffic_light",
    "title": "Вы намерены повернуть направо. Ваши действия?",
    "explanation": "При одновременном праве на движение трамваи имеют преимущество перед безрельсовыми транспортными средствами.(Пункт 13.6 ПДД)",
    "pddRule": "п. 13.6",
    "options": [
      "Проедете перекрёсток первым",
      "Уступите дорогу только трамваю А",
      "Уступите дорогу только трамваю Б",
      "Уступите дорогу обоим трамваям"
    ],
    "correctAnswerIndex": 3,
    "legend": [
      {
        "label": "Вы направо",
        "color": "#ED4621"
      },
      {
        "label": "Трамвай Б",
        "color": "#FFA53C"
      },
      {
        "label": "Трамвай А",
        "color": "#0574F8"
      }
    ],
    "actorsConfig": [
      {
        "id": "tram_b",
        "type": "tram",
        "name": "Трамвай Б",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C",
        "badge": "Б"
      },
      {
        "id": "tram_a",
        "type": "tram",
        "name": "Трамвай А",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#0574F8",
        "badge": "А"
      }
    ],
    "trafficLights": {
      "state": "green"
    },
    "signs": []
  },
  {
    "id": "ticket_40_14",
    "ticket": "Билет 40 · Вопрос 14",
    "type": "crossroad",
    "title": "При движении прямо Вы:",
    "explanation": "Перекрёсток равнозначный. Мигающий маячок оранжевого или жёлтого цвета на грузовике преимуществ его водителю не предоставляет. Водители руководствуются «правилом правой руки». У Вас помеха справа – мотоциклист. Вы уступаете дорогу только мотоциклисту, который начнёт первым движение, выкатится на перекрёсток. После этого Вы проедете через перекрёсток, за Вами грузовик, мотоциклист последним закончит движение.(Пункты 3.4, 13.11 ПДД)",
    "pddRule": "п. 3.4",
    "options": [
      "Имеете преимущество",
      "Должны уступить дорогу только мотоциклу",
      "Должны уступить дорогу только автомобилю",
      "Должны уступить дорогу обоим транспортным средствам"
    ],
    "correctAnswerIndex": 1,
    "legend": [
      {
        "label": "Вы прямо",
        "color": "#ED4621"
      },
      {
        "label": "Мотоцикл",
        "color": "#8B5CF6"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_moto",
        "type": "motorcycle",
        "name": "Мотоцикл",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#8B5CF6"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "opposite",
        "targetAction": "turn_left",
        "color": "#FFA53C",
        "beacon": "amber"
      }
    ],
    "trafficLights": null,
    "signs": []
  },
  {
    "id": "ticket_40_15",
    "ticket": "Билет 40 · Вопрос 15",
    "type": "crossroad_priority_signs",
    "title": "Кому Вы обязаны уступить дорогу при повороте налево?",
    "explanation": "Перед Вами знак 2.4 «Уступите дорогу». Уступаете дорогу транспортным средствам, движущимся по пересекаемой дороге, в данной ситуации обоим транспортным средствам.(Пункт 13.9 ПДД, «Дорожные знаки»)",
    "pddRule": "п. 13.9",
    "options": [
      "Только автобусу",
      "Только грузовому автомобилю",
      "Обоим транспортным средствам"
    ],
    "correctAnswerIndex": 2,
    "legend": [
      {
        "label": "Вы налево",
        "color": "#ED4621"
      },
      {
        "label": "Автобус",
        "color": "#FFA53C"
      },
      {
        "label": "Грузовик",
        "color": "#FFA53C"
      }
    ],
    "actorsConfig": [
      {
        "id": "npc_bus",
        "type": "bus",
        "name": "Автобус",
        "side": "cross_left",
        "targetAction": "straight",
        "color": "#FFA53C"
      },
      {
        "id": "npc_truck",
        "type": "truck",
        "name": "Грузовик",
        "side": "cross_right",
        "targetAction": "straight",
        "color": "#FFA53C"
      }
    ],
    "trafficLights": null,
    "signs": [
      {
        "code": "2.4",
        "name": "Уступите дорогу"
      }
    ]
  },
  {
    "id": "ticket_18_8",
    "ticket": "Билет 18 · Вопрос 8",
    "type": "crossroad_one_way",
    "title": "Вам можно продолжить движение:",
    "explanation": "Стрелка на знаке 5.7.1 «Выезд на дорогу с односторонним движением» указывает направление движения на дороге с односторонним движением. Пересечение дороги не запрещается (траектория «В»). Запрещается поворот налево, т.е. движение во встречном направлении. При повороте направо транспортное средство должно двигаться по возможности ближе к правому краю проезжей части. У Вас такая возможность есть. Можете повернуть по траектории «А».(Пункт 8.6 ПДД, «Дорожные знаки»)",
    "pddRule": "п. 8.6",
    "options": [
      "Только по траектории А",
      "По траекториям А или В",
      "По любой траектории из указанных"
    ],
    "correctAnswerIndex": 1,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": [
      {
        "code": "5.7.1",
        "name": "Выезд на дорогу с односторонним движением"
      }
    ],
    "oneWay": "to_right",
    "trajectories": [
      {
        "label": "А",
        "points": [
          [
            1.8,
            -9
          ],
          [
            1.8,
            -5
          ],
          [
            3.2,
            -2.9
          ],
          [
            6,
            -2.1
          ],
          [
            12,
            -2.1
          ]
        ]
      },
      {
        "label": "Б",
        "points": [
          [
            1.4,
            -9
          ],
          [
            1.4,
            -4
          ],
          [
            3.4,
            0.6
          ],
          [
            6.5,
            2.1
          ],
          [
            12,
            2.1
          ]
        ]
      },
      {
        "label": "В",
        "points": [
          [
            0.9,
            -9
          ],
          [
            0.9,
            0
          ],
          [
            0.9,
            9
          ]
        ]
      }
    ]
  },
  {
    "id": "ticket_14_8",
    "ticket": "Билет 14 · Вопрос 8",
    "type": "crossroad_one_way",
    "title": "По какой траектории Вам разрешается выполнить поворот налево?",
    "explanation": "Согласно знаку 5.7.2 «Выезд на дорогу с односторонним движением» на данном перекрёстке можно продолжить движение прямо, налево и совершить разворот. На дороге с односторонним движением можете двигаться по любой полосе. Поэтому Вам разрешается движение по любой из указанных траекторий.(«Дорожные знаки», пункт 8.6 ПДД)",
    "pddRule": "п. 8.6",
    "options": [
      "Только по А",
      "Только по Б",
      "По любой из указанных"
    ],
    "correctAnswerIndex": 2,
    "legend": [],
    "actorsConfig": [],
    "trafficLights": null,
    "signs": [
      {
        "code": "5.7.2",
        "name": "Выезд на дорогу с односторонним движением"
      }
    ],
    "oneWay": "to_left",
    "trajectories": [
      {
        "label": "А",
        "points": [
          [
            1.4,
            -9
          ],
          [
            1.4,
            -5
          ],
          [
            -0.5,
            -2.6
          ],
          [
            -5,
            -2.1
          ],
          [
            -12,
            -2.1
          ]
        ]
      },
      {
        "label": "Б",
        "points": [
          [
            1.8,
            -9
          ],
          [
            1.8,
            -3
          ],
          [
            0,
            1.4
          ],
          [
            -5,
            2.1
          ],
          [
            -12,
            2.1
          ]
        ]
      }
    ]
  }
];
  SITUATIONS.push(...(window.PDD_EXTRA_SITUATIONS || []));

  // --- Flutter Bridge Helper ---
  function sendToFlutter(messageObj) {
    const json = JSON.stringify(messageObj);
    if (window.FlutterChannel && window.FlutterChannel.postMessage) {
      window.FlutterChannel.postMessage(json);
    } else {
      // Development console fallback
      console.log('[FlutterBridge MSG]:', json);
    }
  }

  // Procedural audio keeps the simulator self-contained and lets every layer
  // react continuously to speed, traffic and distance instead of looping one
  // generic recording at a fixed pitch.
  function createGameAudio() {
    const audio = { enabled: true, paused: false, context: null, master: null,
      nodes: {}, engineLevel: 0, trafficLevel: 0, sirenLevel: 0, tramLevel: 0,
      trackPhase: 0, birdAt: 4, blinkerOn: false };
    const contextClass = window.AudioContext || window.webkitAudioContext;
    const ramp = (param, value, seconds = 0.08) => {
      if (!audio.context || !param) return;
      param.cancelScheduledValues(audio.context.currentTime);
      param.linearRampToValueAtTime(value, audio.context.currentTime + seconds);
    };
    const noiseBuffer = context => {
      const buffer = context.createBuffer(1, context.sampleRate * 2, context.sampleRate);
      const data = buffer.getChannelData(0);
      let last = 0;
      for (let i = 0; i < data.length; i++) {
        last = last * 0.72 + (Math.random() * 2 - 1) * 0.28;
        data[i] = last;
      }
      return buffer;
    };
    const loopNoise = (context, filterType, frequency) => {
      const source = context.createBufferSource();
      source.buffer = noiseBuffer(context); source.loop = true;
      const filter = context.createBiquadFilter();
      filter.type = filterType; filter.frequency.value = frequency;
      const gain = context.createGain(); gain.gain.value = 0;
      source.connect(filter).connect(gain).connect(audio.master); source.start();
      return { source, filter, gain };
    };
    audio.ensure = () => {
      if (!audio.enabled || audio.context || !contextClass) return;
      try {
        const context = new contextClass();
        audio.context = context;
        audio.master = context.createGain(); audio.master.gain.value = 0;
        // No sub-bass: on a phone speaker a 30-60 Hz engine rumble is felt in
        // the hand like vibration while the gas is held.
        const lowCut = context.createBiquadFilter(); lowCut.type = 'highpass'; lowCut.frequency.value = 140; lowCut.Q.value = 0.7;
        audio.master.connect(lowCut).connect(context.destination);
        const makeTone = (type, frequency) => {
          const oscillator = context.createOscillator(); oscillator.type = type; oscillator.frequency.value = frequency;
          const gain = context.createGain(); gain.gain.value = 0;
          oscillator.connect(gain).connect(audio.master); oscillator.start();
          return { oscillator, gain };
        };
        // Engine: sub + fundamental + fifth through one low-pass "exhaust" filter
        // and a gentle soft-clip; the filter opens with rpm/throttle. A band of
        // filtered noise adds combustion grit. Per-vehicle profile scales pitch.
        const engineBus = context.createGain(); engineBus.gain.value = 0;
        const engineFilter = context.createBiquadFilter(); engineFilter.type = 'lowpass';
        engineFilter.frequency.value = 260; engineFilter.Q.value = 1.4;
        const shaper = context.createWaveShaper();
        const curve = new Float32Array(256);
        for (let i = 0; i < 256; i++) { const x = i / 127.5 - 1; curve[i] = Math.tanh(x * 1.8) / Math.tanh(1.8); }
        shaper.curve = curve; shaper.oversample = '2x';
        engineBus.connect(engineFilter).connect(shaper).connect(audio.master);
        const engineVoice = (type, frequency, level) => {
          const oscillator = context.createOscillator(); oscillator.type = type; oscillator.frequency.value = frequency;
          const gain = context.createGain(); gain.gain.value = level;
          oscillator.connect(gain).connect(engineBus); oscillator.start();
          return { oscillator, gain };
        };
        audio.nodes.engineSub = engineVoice('sine', 30, 0.55);
        audio.nodes.engine = engineVoice('sawtooth', 60, 0.5);
        audio.nodes.engineFifth = engineVoice('triangle', 90, 0.28);
        audio.nodes.engineBus = engineBus; audio.nodes.engineFilter = engineFilter;
        audio.nodes.grit = loopNoise(context, 'bandpass', 220);
        audio.nodes.grit.filter.Q.value = 0.9;
        audio.nodes.squeal = loopNoise(context, 'bandpass', 1900);
        audio.nodes.squeal.filter.Q.value = 6;
        audio.nodes.scrape = loopNoise(context, 'bandpass', 520);
        audio.nodes.rain = loopNoise(context, 'highpass', 1600);
        audio.nodes.scrape.filter.Q.value = 1.2;
        audio.rpm = 0.15; audio.reverseBeepAt = 0;
        audio.nodes.traffic = makeTone('triangle', 48);
        audio.nodes.tram = makeTone('sawtooth', 34);
        audio.nodes.sirenLow = makeTone('sine', 620);
        audio.nodes.sirenHigh = makeTone('sine', 820);
        audio.nodes.road = loopNoise(context, 'lowpass', 900);
        audio.nodes.wind = loopNoise(context, 'bandpass', 700);
        audio.nodes.ambience = loopNoise(context, 'lowpass', 420);
      } catch (_) { audio.context = null; }
    };
    // Each garage model has its own voice: pitch, brightness, grit, loudness.
    audio.profiles = {
      hatch: { pitch: 1.18, bright: 1.15, grit: 0.7, level: 0.9 },
      sedan: { pitch: 1.0, bright: 1.0, grit: 0.8, level: 1.0 },
      suv: { pitch: 0.84, bright: 0.85, grit: 1.1, level: 1.1 },
      pickup: { pitch: 0.74, bright: 0.8, grit: 1.4, level: 1.2 },
    };
    audio.profile = audio.profiles.hatch;
    audio.setVehicle = id => { audio.profile = audio.profiles[id] || audio.profiles.hatch; };
    audio.unlock = () => {
      audio.ensure();
      if (audio.context?.state === 'suspended') audio.context.resume().catch(() => {});
    };
    audio.setEnabled = enabled => {
      audio.enabled = Boolean(enabled);
      if (audio.enabled) audio.unlock();
      ramp(audio.master?.gain, audio.enabled && !audio.paused ? 0.72 : 0, 0.12);
    };
    audio.setPaused = paused => {
      audio.paused = Boolean(paused);
      ramp(audio.master?.gain, audio.enabled && !audio.paused ? 0.72 : 0, 0.1);
    };
    audio.transient = (frequency, duration, volume, type = 'sine') => {
      audio.unlock();
      const context = audio.context;
      if (!audio.enabled || !context || audio.paused) return;
      const oscillator = context.createOscillator(), gain = context.createGain();
      oscillator.type = type; oscillator.frequency.setValueAtTime(frequency, context.currentTime);
      oscillator.frequency.exponentialRampToValueAtTime(Math.max(35, frequency * 0.55), context.currentTime + duration);
      gain.gain.setValueAtTime(volume, context.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.0001, context.currentTime + duration);
      oscillator.connect(gain).connect(audio.master); oscillator.start(); oscillator.stop(context.currentTime + duration);
    };
    const burst = (filterType, frequency, q, volume, duration) => {
      const context = audio.context;
      if (!context || !audio.enabled || audio.paused) return;
      const source = context.createBufferSource(), filter = context.createBiquadFilter(), gain = context.createGain();
      source.buffer = noiseBuffer(context); filter.type = filterType; filter.frequency.value = frequency; filter.Q.value = q;
      gain.gain.setValueAtTime(volume, context.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.0001, context.currentTime + duration);
      source.connect(filter).connect(gain).connect(audio.master); source.start(); source.stop(context.currentTime + duration + 0.02);
    };
    // Vehicle-on-vehicle: deep body thump, crunch of panels, a glass tinkle.
    audio.impact = strength => {
      audio.unlock();
      const k = THREE.MathUtils.clamp(strength / 18, 0.25, 1);
      audio.transient(70, 0.42, 0.22 + k * 0.18, 'sine');
      burst('lowpass', 700 + k * 500, 0.7, 0.16 + k * 0.2, 0.32);
      burst('bandpass', 3400, 2.5, 0.05 + k * 0.08, 0.5);
    };
    // A person or a bicycle: dull soft thud, no crunch; the bike adds a short
    // metallic clatter. Deliberately restrained for a driving-school game.
    audio.softImpact = type => {
      audio.unlock();
      audio.transient(120, 0.2, 0.16, 'sine');
      audio.scream();
      burst('lowpass', 380, 0.8, 0.12, 0.18);
      if (type === 'cyclist') { burst('bandpass', 2600, 3, 0.07, 0.35); audio.transient(1700, 0.12, 0.03, 'triangle'); }
    };
    // A short startled cry: a sawtooth "voice" through two vowel formants,
    // pitch falling, quiet and brief — a signal, not a horror effect.
    audio.scream = () => {
      const context = audio.context;
      if (!context || !audio.enabled || audio.paused) return;
      const t0 = context.currentTime;
      const voice = context.createOscillator(); voice.type = 'sawtooth';
      voice.frequency.setValueAtTime(420, t0); voice.frequency.linearRampToValueAtTime(470, t0 + 0.08);
      voice.frequency.exponentialRampToValueAtTime(240, t0 + 0.42);
      const f1 = context.createBiquadFilter(); f1.type = 'bandpass'; f1.frequency.value = 760; f1.Q.value = 5;
      const f2 = context.createBiquadFilter(); f2.type = 'bandpass'; f2.frequency.value = 1300; f2.Q.value = 6;
      const g1 = context.createGain(), g2 = context.createGain(), out = context.createGain();
      g1.gain.value = 0.6; g2.gain.value = 0.35;
      out.gain.setValueAtTime(0.0001, t0); out.gain.linearRampToValueAtTime(0.09, t0 + 0.04);
      out.gain.exponentialRampToValueAtTime(0.0001, t0 + 0.45);
      voice.connect(f1).connect(g1).connect(out); voice.connect(f2).connect(g2).connect(out); out.connect(audio.master);
      voice.start(t0); voice.stop(t0 + 0.47);
    };
    audio.scrapeHit = () => { audio.unlock(); burst('bandpass', 600, 1.5, 0.08, 0.14); };
    audio.beep = () => audio.transient(960, 0.07, 0.03, 'square');
    audio.click = () => audio.transient(1180, 0.035, 0.055, 'square');
    audio.chirp = () => {
      audio.unlock();
      const context = audio.context;
      if (!audio.enabled || !context || audio.paused) return;
      const oscillator = context.createOscillator(), gain = context.createGain();
      oscillator.type = 'sine'; oscillator.frequency.setValueAtTime(1450, context.currentTime);
      oscillator.frequency.linearRampToValueAtTime(2250, context.currentTime + 0.07);
      oscillator.frequency.linearRampToValueAtTime(1650, context.currentTime + 0.16);
      gain.gain.setValueAtTime(0.0001, context.currentTime); gain.gain.linearRampToValueAtTime(0.018, context.currentTime + 0.02);
      gain.gain.exponentialRampToValueAtTime(0.0001, context.currentTime + 0.2);
      oscillator.connect(gain).connect(audio.master); oscillator.start(); oscillator.stop(context.currentTime + 0.21);
    };
    // Celebration sounds for a new car. They bypass the paused game mix
    // (the run is paused while the garage reveal plays).
    audio.celebrate = kind => {
      audio.unlock();
      const context = audio.context;
      if (!audio.enabled || !context) return;
      const out = context.createGain(); out.gain.value = 0.55;
      const lowCut = context.createBiquadFilter(); lowCut.type = 'highpass'; lowCut.frequency.value = 140;
      out.connect(lowCut).connect(context.destination);
      const now = context.currentTime;
      const tone = (freq, at, dur, vol, type = 'sine') => {
        const o = context.createOscillator(), g = context.createGain();
        o.type = type; o.frequency.setValueAtTime(freq, now + at);
        g.gain.setValueAtTime(0.0001, now + at);
        g.gain.linearRampToValueAtTime(vol, now + at + 0.015);
        g.gain.exponentialRampToValueAtTime(0.0001, now + at + dur);
        o.connect(g).connect(out); o.start(now + at); o.stop(now + at + dur + 0.02);
      };
      if (kind === 'door') {
        // A soft mechanical roll: filtered noise swelling and settling.
        const len = 0.3, buffer = context.createBuffer(1, context.sampleRate * len, context.sampleRate);
        const data = buffer.getChannelData(0); for (let i = 0; i < data.length; i++) data[i] = (Math.random() * 2 - 1) * (0.6 + 0.4 * Math.sin(i / 900));
        const src = context.createBufferSource(); src.buffer = buffer;
        const bp = context.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 420; bp.Q.value = 1.1;
        const g = context.createGain(); g.gain.setValueAtTime(0.0001, now); g.gain.linearRampToValueAtTime(0.09, now + 0.2); g.gain.exponentialRampToValueAtTime(0.0001, now + len);
        src.connect(bp).connect(g).connect(out); src.start(now);
        tone(196, 0.24, 0.08, 0.08, 'triangle');
      } else if (kind === 'fanfare') {
        // Major arpeggio up to a held chord, bright and short.
        [[523.25, 0], [659.25, 0.11], [783.99, 0.22], [1046.5, 0.33]].forEach(([f, at]) => { tone(f, at, 0.5, 0.09, 'triangle'); tone(f * 2, at, 0.25, 0.025); });
        [523.25, 659.25, 783.99, 1046.5].forEach(f => tone(f, 0.48, 1.3, 0.06, 'triangle'));
      } else if (kind === 'sparkle') {
        for (let i = 0; i < 6; i++) tone(2200 + Math.random() * 2400, i * 0.07 + Math.random() * 0.03, 0.3, 0.035);
      }
    };
    audio.update = (dt, elapsed) => {
      if (!audio.enabled || audio.paused) return;
      audio.ensure();
      if (!audio.context) return;
      const speedRatio = THREE.MathUtils.clamp(Math.abs(state.speed) / state.maxSpeed, 0, 1);
      const throttle = state.isAccelerating && !state.isBraking ? 1 : 0;
      // Three virtual gears: rpm climbs within a gear and drops at the shift,
      // which is what makes an engine sound like it is working rather than
      // a siren sliding up with speed.
      const gearPos = speedRatio * 2.85, inGear = gearPos - Math.floor(Math.min(2, gearPos));
      const targetRpm = state.speed < -0.2 ? 0.3 : 0.14 + inGear * 0.68 + throttle * 0.08;
      audio.rpm += (targetRpm - audio.rpm) * Math.min(1, dt * (throttle ? 5 : 3));
      const rpm = audio.rpm, pr = audio.profiles[state.vehicleId] || audio.profile;
      const f0 = (52 + rpm * 118) * pr.pitch;
      ramp(audio.nodes.engineSub.oscillator.frequency, f0 / 2);
      ramp(audio.nodes.engine.oscillator.frequency, f0);
      ramp(audio.nodes.engineFifth.oscillator.frequency, f0 * 1.5);
      ramp(audio.nodes.engineFilter.frequency, (240 + rpm * 900 + throttle * 260) * pr.bright);
      audio.engineLevel = (0.05 + rpm * 0.1 + throttle * 0.04) * pr.level;
      ramp(audio.nodes.engineBus.gain, audio.engineLevel);
      ramp(audio.nodes.grit.filter.frequency, 160 + rpm * 260);
      ramp(audio.nodes.grit.gain.gain, (0.012 + rpm * 0.03 + throttle * 0.012) * pr.grit);
      // Tyres: squeal under hard braking from speed, scrape along a curb.
      ramp(audio.nodes.squeal.gain.gain, state.isBraking && state.speed > 6 ? 0.03 + speedRatio * 0.05 : 0, 0.06);
      ramp(audio.nodes.scrape.gain.gain, state.curbClearTime === 0 && Math.abs(state.speed) > 0.5 ? 0.04 : 0, 0.05);
      if (state.speed < -0.3 && elapsed >= audio.reverseBeepAt) { audio.beep(); audio.reverseBeepAt = elapsed + 0.7; }
      // Snow falls silently: only a faint low hush instead of the rain hiss.
      const snowing = season().precipitation === 'snow';
      audio.nodes.rain.filter.frequency.value = snowing ? 380 : 1600;
      ramp(audio.nodes.rain.gain.gain, (state.rain || 0) * (snowing ? 0.006 : 0.045), 0.3);
      ramp(audio.nodes.road.gain.gain, speedRatio * 0.035);
      ramp(audio.nodes.wind.gain.gain, Math.max(0, speedRatio - 0.3) * 0.012);
      ramp(audio.nodes.ambience.gain.gain, 0.013 + (state.district === 1 ? 0.006 : 0));
      const nearby = state.actors.filter(a => !a.done && a.mesh.visible && !a.fall &&
        actorFootprint(a).p.distanceTo(playerCarGroup.position) < 45);
      const trafficEnergy = nearby.reduce((sum, a) => sum + Math.max(0.1, a.speed / Math.max(1, a.maxSpeed)), 0);
      audio.trafficLevel = Math.min(0.055, trafficEnergy * 0.012);
      ramp(audio.nodes.traffic.gain.gain, audio.trafficLevel);
      ramp(audio.nodes.traffic.oscillator.frequency, 45 + trafficEnergy * 7);
      const trams = nearby.filter(a => a.config.type === 'tram' || a.config.type === 'train');
      audio.tramLevel = Math.min(0.07, trams.reduce((sum, a) => sum + a.speed, 0) / 150);
      ramp(audio.nodes.tram.gain.gain, audio.tramLevel);
      audio.trackPhase += dt * trams.reduce((sum, a) => sum + a.speed, 0);
      if (audio.trackPhase > 5.5) { audio.trackPhase %= 5.5; audio.transient(180, 0.045, 0.035, 'square'); }
      const siren = nearby.find(a => a.config.siren && a.active && !a.crashed);
      audio.sirenLevel = siren ? Math.max(0, 1 - actorFootprint(siren).p.distanceTo(playerCarGroup.position) / 45) * 0.11 : 0;
      const high = Math.sin(elapsed * Math.PI * 2.4) > 0;
      ramp(audio.nodes.sirenLow.gain.gain, high ? 0 : audio.sirenLevel, 0.04);
      ramp(audio.nodes.sirenHigh.gain.gain, high ? audio.sirenLevel : 0, 0.04);
      if (elapsed >= audio.birdAt && state.speed < 8 && state.district !== 1) {
        audio.chirp(); audio.birdAt = elapsed + 7 + Math.random() * 8;
      }
      ramp(audio.master.gain, 0.72, 0.15);
    };
    audio.snapshot = () => ({ enabled: audio.enabled, paused: audio.paused,
      engine: audio.engineLevel, traffic: audio.trafficLevel, siren: audio.sirenLevel, tram: audio.tramLevel });
    return audio;
  }

  // --- Initialization ---
  function init() {
    // A native WebView can load before Flutter has given it a layout size.
    // Never put a zero viewport into the camera's projection matrix.
    const width = Math.max(1, container.clientWidth || window.innerWidth);
    const height = Math.max(1, container.clientHeight || window.innerHeight);
    gameAudio = createGameAudio();

    // Scene
    scene = new THREE.Scene();
    scene.background = new THREE.Color(BRAND.asphaltMarking);
    scene.fog = new THREE.FogExp2(BRAND.asphaltMarking, 0.007);

    // Orthographic Camera looking straight forward/up
    const aspect = width / height;
    const viewSize = 42;
    camera = new THREE.OrthographicCamera(
      -viewSize * aspect / 2,
       viewSize * aspect / 2,
       viewSize / 2,
      -viewSize / 2,
      -200,
       800
    );

    // Initial camera position (directly behind and above car looking forward)
    camera.position.set(0, 42, -36);
    camera.lookAt(0, 0, 14);

    // Renderer
    // Weak phones (few cores / little memory) get a cheaper profile: no soft
    // shadow filtering, a smaller shadow map and 1x pixel ratio.
    // iOS WebKit reports a capped hardwareConcurrency (so every iPhone looked
    // "weak" and rendered at 1x without antialiasing — visibly pixelated).
    // Only a clearly weak device (≤2 cores or ≤3 GB) gets the cheap profile.
    const lowEnd = (navigator.hardwareConcurrency || 8) <= 2 || (navigator.deviceMemory || 8) <= 3;
    state.lowEnd = lowEnd;
    renderer = new THREE.WebGLRenderer({ antialias: !lowEnd, powerPreference: 'high-performance' });
    renderer.setSize(width, height);
    renderer.setPixelRatio(lowEnd ? 1 : Math.min(window.devicePixelRatio, 1.75));
    renderer.shadowMap.enabled = true;
    // PCF with a blur radius: soft-edged shadows (PCFSoft ignores radius).
    renderer.shadowMap.type = THREE.PCFShadowMap;
    renderer.localClippingEnabled = true;
    // Road surfaces get their texture phase from the road they continue.
    window.PDD_ROADS.attach(renderer, { roots: () => state.roadSegments, lineage: () => state.exitRoad || currentCorridor });
    container.appendChild(renderer.domElement);

    // Lights
    setupLights();

    // Global continuous terrain ground (no cutoffs ever)
    const groundGeo = new THREE.PlaneGeometry(800, 4000);
    groundGeo.rotateX(-Math.PI / 2);
    const groundMat = new THREE.MeshLambertMaterial({ color: season().ground });
    groundMat.userData.seasonal = 'ground';
    const groundMesh = new THREE.Mesh(groundGeo, groundMat);
    groundMesh.position.set(0, -0.05, 500);
    groundMesh.receiveShadow = true;
    scene.add(groundMesh);
    terrainMesh = groundMesh;

    // Player Car
    playerCarGroup = createPlayerCar();
    playerCarGroup.position.x = -1.8;
    scene.add(playerCarGroup);

    // Build initial road segments
    buildInitialTrack();

    // Event Listeners
    window.addEventListener('resize', onWindowResize);
    setupTouchControls();

    // Hide loader
    const loader = document.getElementById('loading-overlay');
    if (loader) loader.style.display = 'none';

    // Notify Flutter that engine is ready
    sendToFlutter({ event: 'ready', season: seasonName() });

    // Animation Loop
    animate(0);
  }

  // --- Lighting Setup ---
  function setupLights() {
    ambientLight = new THREE.AmbientLight(0xFFFFFF, 0.75);
    scene.add(ambientLight);

    // A high sun: short, soft daytime shadows that read as ground contact,
    // not long dramatic streaks.
    dirLight = new THREE.DirectionalLight(0xFFF9EE, 0.85);
    dirLight.position.set(12, 70, -7);
    dirLight.castShadow = true;
    dirLight.shadow.mapSize.width = state.lowEnd ? 512 : 1024;
    dirLight.shadow.mapSize.height = state.lowEnd ? 512 : 1024;
    dirLight.shadow.camera.near = 10;
    dirLight.shadow.camera.far = 200;
    const d = 40;
    dirLight.shadow.camera.left = -d;
    dirLight.shadow.camera.right = d;
    dirLight.shadow.camera.top = d;
    dirLight.shadow.camera.bottom = -d;
    dirLight.shadow.bias = -0.0005;
    dirLight.shadow.radius = state.lowEnd ? 2 : 5;
    scene.add(dirLight);

    sunTarget = new THREE.Object3D();
    scene.add(sunTarget);
    dirLight.target = sunTarget;
  }

  // --- Actor Floating Badge Factory ---
  function createActorBadge(text, bgColor = '#0574F8') {
    const canvas = document.createElement('canvas');
    canvas.width = 160;
    canvas.height = 70;
    const ctx = canvas.getContext('2d');

    const fill = typeof bgColor === 'number' ? '#' + bgColor.toString(16).padStart(6, '0') : bgColor;
    ctx.fillStyle = fill;
    ctx.beginPath();
    ctx.roundRect(6, 6, 148, 58, 14);
    ctx.fill();

    // Dark text on a light plate (a pale truck body colour), white otherwise.
    const rgb = new THREE.Color(fill);
    const luminance = 0.2126 * rgb.r + 0.7152 * rgb.g + 0.0722 * rgb.b;
    ctx.fillStyle = luminance > 0.55 ? '#121212' : '#FFFFFF';
    ctx.font = '600 28px sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, 80, 35, 138);

    const texture = new THREE.CanvasTexture(canvas);
    texture.minFilter = THREE.LinearFilter;
    const mat = new THREE.SpriteMaterial({ map: texture, depthTest: false });
    const sprite = new THREE.Sprite(mat);
    sprite.scale.set(3.2, 1.25, 1);
    return sprite;
  }

  // A compact round token for trajectory letters: white disc with a soft
  // shadow and a bold brand-blue letter, like the app's chips.
  function createLetterToken(letter) {
    const canvas = document.createElement('canvas');
    canvas.width = canvas.height = 96;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = 'rgba(0, 0, 0, 0.28)';
    ctx.beginPath(); ctx.arc(48, 52, 40, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#FFFFFF';
    ctx.beginPath(); ctx.arc(48, 46, 40, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#0574F8';
    ctx.font = '800 50px sans-serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(letter, 48, 49);
    const texture = new THREE.CanvasTexture(canvas);
    texture.minFilter = THREE.LinearFilter;
    const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: texture, depthTest: false }));
    sprite.renderOrder = 1000;
    sprite.scale.set(1.5, 1.5, 1);
    sprite.userData.trajectoryLabel = letter;
    return sprite;
  }

  // One arrow style for every ticket alternative, including wrong answers.
  // Paths are already in the receiving group's coordinate frame.
  // Route guide: one smooth flat band per route ending in an arrowhead, the
  // same for the player's route and a ticket's labelled alternatives. Kinks
  // between authored points are smoothed out; the ends stay where authored.
  function createRouteGuide(paths) {
    const guide = new THREE.Group();
    const mat = new THREE.MeshBasicMaterial({ color: BRAND.accent, transparent: true, opacity: 0.85, depthWrite: false, side: THREE.DoubleSide });
    const headShape = new THREE.Shape();
    headShape.moveTo(0, 0); headShape.lineTo(-0.5, -1.15); headShape.lineTo(0.5, -1.15); headShape.closePath();
    const headGeo = new THREE.ShapeGeometry(headShape); headGeo.rotateX(Math.PI / 2);
    for (const path of paths) {
      const length = path.getLength(), n = Math.max(8, Math.ceil(length / 0.25));
      let pts = Array.from({ length: n + 1 }, (_, i) => path.getPointAt(i / n));
      for (let pass = 0; pass < 8; pass++) pts = pts.map((p, i) => i === 0 || i === n ? p :
        p.clone().lerp(pts[i - 1].clone().add(pts[i + 1]).multiplyScalar(0.5), 0.5));
      const smooth = curve(pts), total = smooth.getLength(), bodyEnd = Math.max(0.2, total - 0.95);
      const half = 0.16, m = Math.max(2, Math.ceil(bodyEnd / 0.2)), pos = [], idx = [], routePoints = [];
      for (let i = 0; i <= m; i++) {
        const u = bodyEnd * i / m / total, p = smooth.getPointAt(u), t = smooth.getTangentAt(u), l = Math.hypot(t.x, t.z) || 1;
        pos.push(p.x - t.z / l * half, p.y, p.z + t.x / l * half, p.x + t.z / l * half, p.y, p.z - t.x / l * half);
        if (i) idx.push(2 * i - 2, 2 * i, 2 * i - 1, 2 * i - 1, 2 * i, 2 * i + 1);
        routePoints.push([p.x, p.y, p.z]);
      }
      const geo = new THREE.BufferGeometry();
      geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); geo.setIndex(idx);
      const stroke = new THREE.Mesh(geo, mat);
      stroke.userData.routeStroke = true; stroke.userData.routePoints = routePoints;
      guide.add(stroke);
      const tip = smooth.getPointAt(1), dir = smooth.getTangentAt(1);
      const head = new THREE.Mesh(headGeo, mat);
      head.position.copy(tip); head.rotation.y = Math.atan2(dir.x, dir.z);
      head.userData.guideArrow = true;
      guide.add(head);
    }
    return guide;
  }

  // A double-sided advertising board for a roundabout island. The brand is
  // invented for the game (no real trademark), drawn once and shared.
  let billboardTexture = null;
  function createIslandBillboard() {
    if (!billboardTexture) {
      const c = document.createElement('canvas'); c.width = 512; c.height = 256;
      const g = c.getContext('2d'), sky = g.createLinearGradient(0, 0, 0, 256);
      sky.addColorStop(0, '#0F7C86'); sky.addColorStop(1, '#0A4C55');
      g.fillStyle = sky; g.fillRect(0, 0, 512, 256);
      g.fillStyle = 'rgba(255,255,255,0.16)';
      [[60, 200, 14], [92, 160, 9], [120, 214, 6], [440, 60, 16], [404, 104, 10], [470, 128, 7], [300, 40, 8]].forEach(([x, y, r]) => { g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill(); });
      // Bottle: a rounded orange body with a lighter label band.
      g.fillStyle = '#FF8A1F'; g.beginPath();
      g.moveTo(392, 48); g.lineTo(412, 48); g.lineTo(414, 84); g.quadraticCurveTo(446, 104, 444, 140);
      g.lineTo(444, 222); g.quadraticCurveTo(444, 236, 430, 236); g.lineTo(374, 236); g.quadraticCurveTo(360, 236, 360, 222);
      g.lineTo(360, 140); g.quadraticCurveTo(358, 104, 390, 84); g.closePath(); g.fill();
      g.fillStyle = '#FFE2A8'; g.fillRect(360, 150, 84, 40);
      g.fillStyle = '#F4F8F8'; g.font = 'bold 92px Arial, Helvetica, sans-serif'; g.textBaseline = 'alphabetic';
      g.fillText('BULBO', 34, 138);
      g.fillStyle = '#FFB866'; g.font = 'bold 44px Arial, Helvetica, sans-serif'; g.fillText('cola', 38, 196);
      g.strokeStyle = '#F4F8F8'; g.lineWidth = 8; g.strokeRect(4, 4, 504, 248);
      billboardTexture = new THREE.CanvasTexture(c);
      billboardTexture.anisotropy = Math.min(4, renderer.capabilities.getMaxAnisotropy());
      signTextureCache.set('billboard:bulbo', billboardTexture); // shared: never disposed with a segment
    }
    const group = new THREE.Group(), metal = sceneryMat(0x4A5359);
    const parts = [];
    for (const x of [-1.5, 1.5]) { const post = new THREE.Mesh(new THREE.BoxGeometry(0.16, 2.6, 0.16)); post.position.set(x, 1.3, 0); parts.push(post); }
    const frame = new THREE.Mesh(new THREE.BoxGeometry(4.8, 2.5, 0.16)); frame.position.set(0, 3.75, 0); parts.push(frame);
    const frameMesh = mergeStatic(parts, metal); frameMesh.castShadow = true; group.add(frameMesh);
    parts.forEach(m => m.geometry.dispose());
    const faceMat = new THREE.MeshLambertMaterial({ map: billboardTexture });
    for (const side of [-1, 1]) {
      const face = new THREE.Mesh(new THREE.PlaneGeometry(4.6, 2.3), faceMat);
      face.position.set(0, 3.75, side * 0.085); face.rotation.y = side < 0 ? Math.PI : 0;
      group.add(face);
    }
    group.userData.sceneryObject = true; group.userData.billboard = true;
    return group;
  }

  // --- Touch & Gesture Controls ---
  let touchStartX = 0, touchStartY = 0;

  // Player camera zoom: multiplies the framed view size (<1 closer, >1 farther).
  // Works while driving and while a question is open; pinch, wheel, +/- keys,
  // or window.setGameZoom() for native buttons.
  const ZOOM_MIN = 0.45, ZOOM_MAX = 1.6;
  state.userZoom = 1;
  state.questionCameraPan = new THREE.Vector3();
  function questionCameraOpen() { return !reveal&&!!state.isAtSituation&&!state.isResolvingSituation&&!state.attract; }
  function resetQuestionCamera() {
    state.userZoom = 1; state.questionCameraPan.set(0,0,0); state.questionZoomAnchor = null;state.questionCameraBounds=null;state.questionCameraInspecting=false;
  }
  function constrainQuestionPan(pan) {
    const b=state.questionCameraBounds;
    if(!b)return pan.set(0,0,0);
    const side=THREE.MathUtils.clamp(pan.dot(b.right),-b.side,b.side);
    const along=THREE.MathUtils.clamp(pan.dot(b.forward),-b.along,b.along);
    return pan.copy(b.right).multiplyScalar(side).addScaledVector(b.forward,along);
  }
  function cameraGroundAt(clientX, clientY) {
    const rect=renderer.domElement.getBoundingClientRect();
    if (!rect.width || !rect.height) return null;
    const screen=new THREE.Vector2((clientX-rect.left)/rect.width*2-1,1-(clientY-rect.top)/rect.height*2);
    camera.updateMatrixWorld(true);
    const ray=new THREE.Raycaster();ray.setFromCamera(screen,camera);
    const point=ray.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0,1,0),0),new THREE.Vector3());
    return point ? {point,screen} : null;
  }
  function zoomAt(z,from,to=from) {
    if (questionCameraOpen()) {
      state.questionCameraInspecting=true;
      const anchor=cameraGroundAt(from.x,from.y),target=cameraGroundAt(to.x,to.y);
      if(anchor&&target){
        // Several touch events can arrive before the next render. Continue
        // from the pending anchor rather than dropping the earlier movement.
        const previous=state.questionZoomAnchor;
        state.questionZoomAnchor={point:previous&&previous.screen.distanceTo(anchor.screen)<1e-6?previous.point:anchor.point,screen:target.screen};
      }
    }
    return setUserZoom(z);
  }
  function setUserZoom(z) {
    if(questionCameraOpen()&&z!==state.userZoom)state.questionCameraInspecting=true;
    state.userZoom = Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, z)); return state.userZoom;
  }
  window.setGameZoom = (z) => setUserZoom(Number(z) || 1);
  window.changeGameZoom = (factor) => setUserZoom(state.userZoom * (Number(factor) || 1));

  function setupZoomControls() {
    const el = renderer.domElement;
    let pinchDist = 0, lastPoint = null, cameraGesture = false;
    const dist = (t) => Math.hypot(t[0].clientX - t[1].clientX, t[0].clientY - t[1].clientY);
    const midpoint=t=>({x:(t[0].clientX+t[1].clientX)/2,y:(t[0].clientY+t[1].clientY)/2});
    el.addEventListener('touchstart', (e) => {
      if (reveal) { cameraGesture=false;pinchDist=0;lastPoint=null;return; }
      if (e.touches.length === 2) { cameraGesture=true;pinchDist = dist(e.touches); lastPoint=midpoint(e.touches); state.isAccelerating = false; }
      else if(e.touches.length===1&&questionCameraOpen()){cameraGesture=true;lastPoint={x:e.touches[0].clientX,y:e.touches[0].clientY};}
    }, { passive: true });
    el.addEventListener('touchmove', (e) => {
      if (e.touches.length === 2 && pinchDist) {
        const d=dist(e.touches),point=midpoint(e.touches);
        if(d>0){zoomAt(state.userZoom*pinchDist/d,lastPoint||point,point);pinchDist=d;lastPoint=point;}
      } else if(e.touches.length===1&&questionCameraOpen()&&lastPoint) {
        const point={x:e.touches[0].clientX,y:e.touches[0].clientY};zoomAt(state.userZoom,lastPoint,point);lastPoint=point;
      } else return;
      e.preventDefault();
    }, { passive: false });
    const endGesture=e=>{
      e.handledByCamera=cameraGesture;
      if(e.touches.length<2)pinchDist=0;
      lastPoint=e.touches.length===1?{x:e.touches[0].clientX,y:e.touches[0].clientY}:null;
      if(!e.touches.length)cameraGesture=false;
    };
    el.addEventListener('touchend',endGesture,{passive:true});el.addEventListener('touchcancel',endGesture,{passive:true});
    el.addEventListener('wheel', (e) => {
      if (reveal) { e.preventDefault();return; }
      zoomAt(state.userZoom*Math.exp(e.deltaY*0.0012),{x:e.clientX,y:e.clientY});
      e.preventDefault();
    }, { passive: false });
    let mousePoint=null;
    el.addEventListener('mousedown',e=>{if(e.button===0&&questionCameraOpen())mousePoint={x:e.clientX,y:e.clientY};});
    window.addEventListener('mousemove',e=>{
      if(!mousePoint||!questionCameraOpen())return;
      const point={x:e.clientX,y:e.clientY};zoomAt(state.userZoom,mousePoint,point);mousePoint=point;
    });
    window.addEventListener('mouseup',()=>{mousePoint=null;});
    window.addEventListener('keydown', (e) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      if (e.key === '+' || e.key === '=') setUserZoom(state.userZoom / 1.15);
      else if (e.key === '-' || e.key === '_') setUserZoom(state.userZoom * 1.15);
    });
  }

  function setupTouchControls() {
    const el = renderer.domElement;
    setupZoomControls();

    // Acceleration on press
    el.addEventListener('touchstart', (e) => {
      if (e.touches.length > 0) { state.dragX = e.touches[0].clientX; state.dragMoved = 0; }
      if (state.nativeControls) return;
      if (e.touches.length > 1) { state.isAccelerating = false; e.preventDefault(); return; }
      e.preventDefault();
      if (!state.paused && !state.isAtSituation && !state.isResolvingSituation) state.isAccelerating = true;
      if (e.touches.length > 0) {
        touchStartX = e.touches[0].clientX;
        touchStartY = e.touches[0].clientY;
      }
    }, { passive: false });

    el.addEventListener('touchmove', (e) => {
      if (!e.touches.length || !(state.attract || reveal)) return;
      const x = e.touches[0].clientX, dx = x - (state.dragX ?? x); state.dragX = x; state.dragMoved = (state.dragMoved || 0) + Math.abs(dx);
      if (reveal) { if (reveal.phase === 'shown' || reveal.phase === 'lobby') { reveal.yaw += dx * 0.012; reveal.spin = dx * 0.6; } }
      else state.orbitYaw = (state.orbitYaw || 0) + dx * 0.006;
      e.preventDefault();
    }, { passive: false });
    el.addEventListener('touchend', (e) => {
      if(e.handledByCamera){state.isAccelerating=false;return;}
      if (reveal) {
        if (!e.touches.length && (state.dragMoved || 0) < 12) window.game.openReveal();
        state.isAccelerating=false;return;
      }
      if (state.nativeControls) return;
      e.preventDefault();
      state.isAccelerating = false;
      if (e.changedTouches.length > 0) {
        const dx = e.changedTouches[0].clientX - touchStartX;
        const dy = e.changedTouches[0].clientY - touchStartY;
        // Horizontal swipe: change lane
        if (Math.abs(dx) > 35 && Math.abs(dx) > Math.abs(dy)) {
          if (dx > 0) switchLane('right');
          else switchLane('left');
        }
      }
    }, { passive: false });

    el.addEventListener('touchcancel', () => {
      if (state.nativeControls) return;
      state.isAccelerating = false;
    });

    // Mouse fallback for testing
    el.addEventListener('click', () => { if (reveal) window.game.openReveal(); });
    el.addEventListener('mousedown', () => { if (!state.nativeControls && !state.paused && !state.isAtSituation && !state.isResolvingSituation) state.isAccelerating = true; });
    window.addEventListener('mouseup', () => { if (!state.nativeControls) state.isAccelerating = false; });
  }

  function switchLane(direction) {
    if (state.paused || state.isAtSituation || state.isResolvingSituation) return;
    if (direction === 'left' && state.targetLane > 0) {
      state.targetLane--;
      triggerBlinker('left');
    } else if (direction === 'right' && state.targetLane < 1) {
      state.targetLane++;
      triggerBlinker('right');
    }
    // With forward = +Z, the driver's right is -X (also screen-right).
    state.targetLaneOffset = (state.targetLane === 0 ? 1.8 : -1.8);
  }

  function triggerBlinker(side) {
    if (!playerCarGroup) return;
    const blinker = side === 'left' ? playerCarGroup.blinkerL : playerCarGroup.blinkerR;
    if (!blinker) return;
    state.blinker = { side, remaining: 2.2, elapsed: 0 };
  }

  // --- Low-Poly Car Factory ---
  function createPlayerCar() {
    const car = window.PDD_VEHICLES.create(state.vehicleId || "hatch", state.vehiclePaint || null);
    playerWheels = car.userData.wheels;
    return car;
  }

  function selectVehicle(id, paint = null) {
    if (!window.PDD_VEHICLES.specs[id]) return;
    // Never silently drop a choice: while moving it is applied once stopped.
    if (!state.paused && Math.abs(state.speed) > 0.1) { state.pendingVehicle = [id, paint]; return; }
    state.pendingVehicle = null;
    state.speed = 0; state.isAccelerating = false; state.isBraking = false; state.steering = 0; state.laneChangeX = null; state.autoPath = null; state.trail = [];
    if (state.vehicleId === id && (state.vehiclePaint || null) === (paint || null)) {
      sendToFlutter({ event: 'vehicle_selected', vehicleId: id, paint: state.vehiclePaint });
      return;
    }
    const previous = playerCarGroup;
    const previousId = state.vehicleId || 'hatch', previousPaint = state.vehiclePaint || null;
    state.vehicleId = id; state.vehiclePaint = paint || null;
    gameAudio?.setVehicle(id);
    playerCarGroup = createPlayerCar();
    playerCarGroup.position.copy(previous.position);
    playerCarGroup.quaternion.copy(previous.quaternion);
    // A larger body must fit before it replaces the old one. Find the closest
    // free position without turning the car or moving any surrounding traffic.
    const free = () => playerOnRoad() && !state.actors.some(a => !a.done && !a.fall &&
      footprintsOverlap(playerFootprint(), actorFootprint(a), 0.05));
    let fits = free();
    for (let radius = 0.1; !fits && radius <= 3; radius += 0.1) {
      for (let i = 0; i < 32; i++) {
        const angle = i * Math.PI / 16;
        playerCarGroup.position.copy(previous.position).add(new THREE.Vector3(Math.cos(angle) * radius, 0, Math.sin(angle) * radius));
        if (free()) { fits = true; break; }
      }
    }
    if (!fits) {
      disposeSegment(playerCarGroup);
      playerCarGroup = previous;
      playerWheels = previous.userData.wheels;
      state.vehicleId = previousId; state.vehiclePaint = previousPaint;
      sendToFlutter({ event: 'vehicle_selected', vehicleId: previousId, paint: previousPaint });
      return;
    }
    scene.add(playerCarGroup);
    disposeSegment(previous);
    sendToFlutter({ event: 'vehicle_selected', vehicleId: id, paint: state.vehiclePaint });
    renderer.render(scene, camera);
  }

  // Shared surface atlases leave physical geometry and workshop part indices
  // intact. A tyre geometry can be reused by several wheels: remap it once.
  function transportMaterial(kind, color) {
    const surfaces = window.PDD_VEHICLE_MATERIALS;
    return surfaces.material('paint', color, surfaces.transportMap(kind));
  }
  function transportMesh(geometry, material) {
    const surfaces = window.PDD_VEHICLE_MATERIALS;
    geometry.userData = geometry.userData || {};
    if (!geometry.userData.vehicleUV) {
      if (material.map?.name.startsWith('vehicle:transport:') && geometry.type === 'BoxGeometry') {
        surfaces.transportBoxUV(geometry); geometry.userData.vehicleUV = true;
      } else if (['rubber', 'rubberFarm'].includes(material.userData.vehicleSurface) && geometry.type === 'CylinderGeometry') {
        surfaces.tyreUV(geometry); geometry.userData.vehicleUV = true;
      }
    }
    return new THREE.Mesh(geometry, material);
  }

  // A continuous side outline in (z,y), centred across X. Used for shaped
  // van bodies, tanks and mudguards, rather than stacked rectangular blocks.
  function transportProfile(points, width, material, bevel = 0.035) {
    const shape = new THREE.Shape();
    shape.moveTo(...points[0]); points.slice(1).forEach(p => shape.lineTo(...p)); shape.closePath();
    const depth = width - 2 * bevel;
    const geometry = new THREE.ExtrudeGeometry(shape, {depth, bevelEnabled: bevel > 0,
      bevelThickness: bevel, bevelSize: bevel, bevelSegments: 1, curveSegments: 3});
    geometry.rotateY(-Math.PI / 2); geometry.translate(depth / 2, 0, 0);
    const mesh = new THREE.Mesh(geometry, material); mesh.castShadow = true;
    return mesh;
  }
  function transportGlassQuad(points, material, uAxis = 'x') {
    const [a,b,c,d] = points, geometry = new THREE.BufferGeometry();
    geometry.setAttribute('position', new THREE.Float32BufferAttribute([...a,...b,...c,...a,...c,...d],3));
    geometry.computeVertexNormals(); window.PDD_VEHICLE_MATERIALS.glassUV(geometry,uAxis,'y');
    return new THREE.Mesh(geometry,material);
  }
  function mergeTransportParts(group) {
    // Only fixed parts with the exact same material. Moving wheels, riders,
    // cab panes and named pose anchors keep their independent transforms.
    const batches = new Map();
    group.children.filter(o => o.isMesh && !o.children.length && !o.name &&
      !group.userData.wheels?.includes(o) && !group.userData.cabWindows?.includes(o)).forEach(o => {
      if (!batches.has(o.material)) batches.set(o.material, []);
      batches.get(o.material).push(o);
    });
    batches.forEach((parts, material) => {
      if (parts.length < 2) return;
      const merged = mergeStatic(parts,material); merged.castShadow = true;
      parts.forEach(p => {group.remove(p);p.geometry.dispose();}); group.add(merged);
    });
  }

  // --- Tram Model Factory ---
  function createTram(color = BRAND.tramRed) {
    const tram = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const bodyMat = transportMaterial('tram-body', color);
    const whiteMat = transportMaterial('roof', BRAND.tramWhite);
    const glassMat = V.material('glass', 0xffffff, V.transportMap('tram-windows'));
    const metalMat = V.material('metal', 0x71717A);

    // Lower body (color)
    const lowerGeo = new THREE.BoxGeometry(2.2, 1.0, 9.5);
    const lower = transportMesh(lowerGeo, bodyMat);
    lower.position.y = 0.7;
    lower.castShadow = true;
    tram.add(lower);
    tram.userData.lampSpec = { front: { x: 0.6, y: 0.75, z: 4.75 }, rear: { x: 0.6, y: 0.75, z: -4.75 } };

    // Upper stripe / roof (white)
    const upperGeo = new THREE.BoxGeometry(2.15, 1.1, 9.4);
    const upper = transportMesh(upperGeo, whiteMat);
    upper.position.y = 1.7;
    upper.castShadow = true;
    tram.add(upper);

    // Continuous glass strip on sides
    const sideWindowsGeo = new THREE.BoxGeometry(2.24, 0.65, 8.8);
    const sideWindows = transportMesh(sideWindowsGeo, glassMat);
    sideWindows.position.y = 1.75;
    tram.add(sideWindows);

    // Front/Back glass
    const frontGlassGeo = new THREE.BoxGeometry(1.9, 0.8, 0.1);
    const fg = transportMesh(frontGlassGeo, glassMat);
    fg.position.set(0, 1.65, 4.76);
    tram.add(fg);

    // Pantograph (current collector on roof)
    const pantoBase = transportMesh(new THREE.BoxGeometry(0.8, 0.15, 0.8), metalMat);
    pantoBase.position.set(0, 2.35, 1.5);
    tram.add(pantoBase);

    const barGeo = new THREE.CylinderGeometry(0.04, 0.04, 1.1);
    const bar1 = transportMesh(barGeo, metalMat);
    bar1.position.set(0, 2.85, 1.5);
    bar1.rotation.x = 0.35;
    tram.add(bar1);

    const headGeo = new THREE.BoxGeometry(1.6, 0.06, 0.2);
    const head = transportMesh(headGeo, metalMat);
    head.position.set(0, 3.3, 1.7);
    tram.add(head);

    return tram;
  }

  // --- NPC Car Factory ---
  // Details that turn a box into a car: bumpers, grille, head/tail lights,
  // mirrors, rims, side windows and a door line. Coordinates: +Z = front.
  function addVehicleDetails(group, o) {
    const V = window.PDD_VEHICLE_MATERIALS;
    const dark = V.material('metal', 0x23272C);
    const chrome = V.material('metal', 0xC9D1D6), steel = V.material('steelRim', 0xC9D1D6);
    group.userData.rims = [];
    const head = V.material('lens', 0xFFF3CC), tail = V.material('lens', 0xD33D38);
    const glass = V.material('glass', 0xffffff);
    const box = (w, h, d, x, y, z, mat) => { const m = transportMesh(new THREE.BoxGeometry(w, h, d), mat); m.position.set(x, y, z); group.add(m); return m; };
    const { width: W, length: L, baseY, lampY, cabinY, cabinH, cabinZ, cabinL } = o;
    box(W + 0.06, 0.16, 0.18, 0, baseY - 0.16, L / 2 - 0.02, dark);   // front bumper
    box(W + 0.06, 0.16, 0.18, 0, baseY - 0.16, -L / 2 + 0.02, dark);  // rear bumper
    box(W * 0.42, 0.14, 0.04, 0, lampY, L / 2 + 0.02, V.material('grille', 0x23272C));          // grille
    [-1, 1].forEach(sx => {
      box(0.32, 0.13, 0.05, sx * W * 0.34, lampY, L / 2 + 0.03, head);
      box(0.3, 0.12, 0.05, sx * W * 0.34, lampY, -L / 2 - 0.03, tail);
      box(0.05, 0.05, 0.1, sx * W * 0.34, lampY - 0.11, -L / 2 - 0.02, chrome); // exhaust hint / reflector
      const mirror = box(0.08, 0.1, 0.16, sx * (W / 2 + 0.1), cabinY + 0.05, cabinZ + cabinL / 2 - 0.15, dark);
      mirror.rotation.y = sx * 0.2;
      if (cabinH) {
        box(0.02, cabinH * 0.62, cabinL * 0.82, sx * (o.cabinW / 2 + 0.005), cabinY + cabinH * 0.06, cabinZ, glass); // side windows
        box(0.02, baseY * 0.9, 0.03, sx * (W / 2 + 0.005), baseY, cabinZ + 0.1, dark);                              // door line
      }
    });
    if (o.wheels) o.wheels.forEach(w => {
      const rim = transportMesh(new THREE.CylinderGeometry(o.wheelR * 0.55, o.wheelR * 0.55, o.wheelW + 0.02, 8).rotateZ(Math.PI / 2), steel);
      rim.position.copy(w.position); group.add(rim); group.userData.rims.push(rim);
    });
  }

  // Traffic and parked cars use the same detailed bodies as the player's
  // cars (hatchback, saloon or estate), in the scenario's colour.
  const NPC_MODELS = ['sedan', 'hatch', 'wagon', 'sedan'];
  function createNpcCar(color = 0x2BC280) {
    const id = NPC_MODELS[Math.floor(Math.random() * NPC_MODELS.length)];
    return window.PDD_VEHICLES.create(id, color);
  }

  // --- Delivery van (a courier "bus" in the tickets' photos) ---
  function createVan(color = 0xF2C230) {
    const van = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const paint = transportMaterial('van-profile',color), glass = V.material('glass',0x8497A3);
    const trim = V.material('rubberRound',0x252B31), metal = V.material('metal',0xBAC4CB);
    const tyre = V.material('rubber',0x18181B), steel = V.material('steelRim',0xC9D1D6);
    const head = V.material('lens',0xFFF3CC), tail = V.material('lens',0xD33D38);
    const add = m => {m.castShadow=true;van.add(m);return m;};
    const box = (size,mat,x,y,z) => {const m=transportMesh(new THREE.BoxGeometry(...size),mat);m.position.set(x,y,z);return add(m);};
    // A single panel-van shell: wheel cutouts, sloping screen, short bonnet
    // and continuous cargo roof. No delivery box perched behind a tiny cab.
    const profile = [[-2.35,.40],[-1.98,.40]];
    for (const z of [-1.53,1.55]) {
      for(let i=0;i<=12;i++){const a=Math.PI-i*Math.PI/12;profile.push([z+.44*Math.cos(a),.36+.44*Math.sin(a)]);}
    }
    profile.push([2.34,.40],[2.36,1.03],[1.92,1.28],[1.24,1.90],[.96,2.04],[-2.22,2.04],[-2.35,1.91]);
    const shell = add(transportProfile(profile,1.88,paint,.035));shell.name='van-shell';
    V.transportProfileUV(shell.geometry,1.88,4.9,.35,2.10);
    // Glazing follows the shell exactly, with room for the A/B pillars.
    add(transportGlassQuad([[-.79,1.42,1.85],[.79,1.42,1.85],[.79,1.88,1.34],[-.79,1.88,1.34]],glass)).name='van-windscreen';
    for(const side of [-1,1]) {
      const x=side*.945;
      add(transportGlassQuad([[x,1.38,.46],[x,1.38,1.76],[x,1.88,1.20],[x,1.88,.46]],glass,'z')).name='van-side-window';
      box([.055,.055,.25],metal,side*.975,1.35,1.39);
      box([.10,.15,.20],trim,side*1.04,1.39,1.37);
    }
    box([1.93,.14,.18],trim,0,.48,2.36);box([1.93,.14,.18],trim,0,.48,-2.35);
    box([.91,.20,.045],V.material('grille',0x252B31),0,.93,2.405);
    for(const side of [-1,1]) {
      box([.34,.16,.055],head,side*.67,.95,2.409);
      box([.16,.47,.035],tail,side*.78,1.11,-2.395);
    }
    box([.46,.10,.02],V.material('plate',0xE8ECEF),0,.59,2.457);
    box([.46,.10,.02],V.material('plate',0xE8ECEF),0,1.12,-2.409);
    box([.014,1.47,.012],V.material('paint',new THREE.Color(color).multiplyScalar(.65)),0,1.18,-2.395);
    for(const x of [-.13,.13])box([.065,.11,.022],trim,x,1.23,-2.402);
    van.userData.wheels=[];
    const geo = new THREE.CylinderGeometry(.36,.36,.26,20).rotateZ(Math.PI/2);
    for(const z of [1.55,-1.53])for(const side of [-1,1]) {
      const w=transportMesh(geo,tyre);w.position.set(side*.87,.36,z);add(w);van.userData.wheels.push(w);
      const rim=transportMesh(new THREE.CylinderGeometry(.215,.215,.026,16).rotateZ(Math.PI/2),steel);
      rim.position.x=side*.145;w.add(rim);
    }
    van.userData.lampSpec={front:{x:.65,y:.95,z:2.44},rear:{x:.60,y:1.10,z:-2.42}};
    van.userData.modelVersion=2;
    return van;
  }


  // --- Bus Model Factory ---
  function createBus(color = 0xF59E0B) {
    const bus = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const bodyMat = transportMaterial('bus-body', color);
    const roofMat = transportMaterial('roof', 0xF1F5F9);
    const glassMat = V.material('glass', 0xffffff, V.transportMap('bus-windows'));
    const darkMat = transportMaterial('hvac', 0x334155);
    const wheelMat = V.material('rubber', 0x18181B);
    const lightMat = V.material('lens', 0xFEF08A);

    // Lower & main body
    const body = transportMesh(new THREE.BoxGeometry(2.15, 1.4, 6.8), bodyMat);
    body.position.y = 1.0;
    body.castShadow = true;
    bus.add(body);
    bus.userData.lampSpec = { front: { x: 0.75, y: 0.75, z: 3.4 }, rear: { x: 0.75, y: 0.95, z: -3.4 } };

    // Upper roof
    const roof = transportMesh(new THREE.BoxGeometry(2.1, 0.4, 6.7), roofMat);
    roof.position.y = 1.85;
    roof.castShadow = true;
    bus.add(roof);

    // AC unit on roof
    const ac = transportMesh(new THREE.BoxGeometry(1.2, 0.25, 2.0), darkMat);
    ac.position.set(0, 2.15, 0.4);
    bus.add(ac);

    // Side windows strip
    const sideGlass = transportMesh(new THREE.BoxGeometry(2.18, 0.65, 6.2), glassMat);
    sideGlass.position.y = 1.45;
    bus.add(sideGlass);

    // Front windshield
    const frontGlass = transportMesh(new THREE.BoxGeometry(2.0, 0.85, 0.1), glassMat);
    frontGlass.position.set(0, 1.4, 3.41);
    bus.add(frontGlass);

    // Front Headlights
    [-0.8, 0.8].forEach(x => {
      const hl = transportMesh(new THREE.BoxGeometry(0.3, 0.2, 0.08), lightMat);
      hl.position.set(x, 0.6, 3.42);
      bus.add(hl);
    });

    // Wheels
    const wheelGeo = new THREE.CylinderGeometry(0.42, 0.42, 0.3, 12);
    wheelGeo.rotateZ(Math.PI / 2);
    const wheels = [[-1.0, 0.42, 2.1], [1.0, 0.42, 2.1], [-1.0, 0.42, -1.8], [1.0, 0.42, -1.8]].map(p => {
      const w = transportMesh(wheelGeo, wheelMat);
      w.position.set(p[0], p[1], p[2]);
      bus.add(w); return w;
    });
    const dark = V.material('metal', 0x23272C), chrome = V.material('steelRim', 0xC9D1D6);
    const put = (geo, mat, x, y, z) => { const m = transportMesh(geo, mat); m.position.set(x, y, z); bus.add(m); return m; };
    put(new THREE.BoxGeometry(2.2, 0.16, 0.2), dark, 0, 0.35, 3.42);
    put(new THREE.BoxGeometry(2.2, 0.16, 0.2), dark, 0, 0.35, -3.42);
    [-1, 1].forEach(sx => {
      put(new THREE.BoxGeometry(0.3, 0.16, 0.06), V.material('lens', 0xD33D38), sx * 0.8, 0.7, -3.43);
      put(new THREE.BoxGeometry(0.1, 0.22, 0.2), dark, sx * 1.18, 1.55, 3.1);
    });
    put(new THREE.BoxGeometry(0.02, 1.2, 0.9), V.material('glass', 0xffffff), -1.09, 0.95, 1.4); // door (right side)
    bus.userData.wheels = wheels; bus.userData.rims = [];
    wheels.forEach(w => { const rim = put(new THREE.CylinderGeometry(0.22, 0.22, 0.32, 8).rotateZ(Math.PI / 2), chrome, 0, 0, 0); rim.position.copy(w.position); bus.userData.rims.push(rim); });

    return bus;
  }

  // --- Truck Model Factory ---
  // Farm tractor: big rear wheels, small front wheels, narrow bonnet, open
  // cab with a roof, exhaust stack. Faces +Z like every other vehicle.
  function createTractor(color = 0xF2B233) {
    const t=new THREE.Group(),V=window.PDD_VEHICLE_MATERIALS;
    const paint=V.material('paint',color),hood=transportMaterial('tractor',color);
    const dark=V.material('metal',0x2B2F33),rim=V.material('steelRim',0xD9D2C0),glass=V.material('glass',0x8497A3);
    const add=(m,x=0,y=0,z=0)=>{m.position.set(x,y,z);m.castShadow=true;t.add(m);return m;};
    const box=(size,mat,x,y,z)=>add(transportMesh(new THREE.BoxGeometry(...size),mat),x,y,z);
    const bonnet=transportProfile([[.33,.77],[2.25,.77],[2.25,1.31],[2.08,1.47],[.38,1.49]],1.05,hood,.04);
    V.transportProfileUV(bonnet.geometry,1.05,4,.6,1.55);add(bonnet);
    box([1.06,.40,.035],V.material('grille',0x252B31),0,1.04,2.30);
    box([1.45,.45,1.66],paint,0,1.20,-.43); // solid lower cab supports every pane
    box([1.60,.16,1.87],paint,0,2.79,-.43); // roof covers the four corner posts
    const rearZ=-1.22,frontZ=.36;
    for(const x of [-.70,.70])for(const z of [rearZ,frontZ])box([.08,1.36,.08],dark,x,2.03,z);
    for(const z of [rearZ,frontZ])for(const y of [1.47,2.66])box([1.48,.08,.08],dark,0,y,z);
    for(const x of [-.70,.70])for(const y of [1.47,2.66])box([.08,.08,1.66],dark,x,y,-.43);
    t.userData.cabWindows=[
      box([1.30,1.10,.018],glass,0,2.065,.391),
      box([1.30,1.10,.018],glass,0,2.065,-1.251),
      box([.018,1.10,1.48],glass,-.731,2.065,-.43),
      box([.018,1.10,1.48],glass,.731,2.065,-.43)
    ];
    for(const side of [-1,1]) {
      box([.035,.04,.19],dark,side*.747,1.55,-.03); // door handles on the frame
      box([.28,.10,.57],dark,side*.82,.66,-.23); // cab access steps
      // Shaped rear mudguards sit over, rather than through, the large tyres.
      const points=[];
      for(let i=0;i<=12;i++){const a=.20*Math.PI+i*.60*Math.PI/12;points.push([-.70+.93*Math.cos(a),.85+.93*Math.sin(a)]);}
      for(let i=12;i>=0;i--){const a=.20*Math.PI+i*.60*Math.PI/12;points.push([-.70+.85*Math.cos(a),.85+.85*Math.sin(a)]);}
      add(transportProfile(points,.39,paint,0),side*.995);
      box([.19,.15,.045],V.material('lens',0xFFF3CC),side*.35,1.26,2.326);
      box([.14,.11,.035],V.material('lens',0xD33D38),side*.57,1.13,-1.282);
    }
    add(transportMesh(new THREE.CylinderGeometry(.055,.055,1.00,8),dark),.43,2.02,1.72);
    box([.13,.06,.14],dark,.43,2.55,1.72);
    const wheel=(r,w,x,z)=>{
      const m=transportMesh(new THREE.CylinderGeometry(r,r,w,20).rotateZ(Math.PI/2),V.material('rubberFarm',0x22282D));add(m,x,r,z);
      const cap=transportMesh(new THREE.CylinderGeometry(r*.55,r*.55,.035,16).rotateZ(Math.PI/2),rim);cap.position.x=Math.sign(x)*(w/2+.02);m.add(cap);return m;
    };
    t.userData.wheels=[wheel(.85,.50,-.95,-.70),wheel(.85,.50,.95,-.70),wheel(.42,.30,-.70,1.60),wheel(.42,.30,.70,1.60)];
    t.userData.lampSpec={front:{x:.35,y:1.26,z:2.33},rear:{x:.57,y:1.13,z:-1.30}};
    t.userData.modelVersion=2;
    mergeTransportParts(t);
    return t;
  }


  // A horse-drawn cart (гужевая повозка, tickets 12.11 and 30.14): a trotting
  // horse in shafts, a wooden cart with sacks and the driver on the front
  // board. Faces +Z, centred on the origin like every actor model. The legs
  // swing with the actor's gait (diagonal pairs: a trot); no indicators.
  function createHorseCart(color = 0x8B5A2B) {
    const c = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const coat = new THREE.MeshLambertMaterial({ color });
    const mane = new THREE.MeshLambertMaterial({ color: 0x3A2618 });
    const hoof = new THREE.MeshLambertMaterial({ color: 0x2A2420 });
    const wood = V.material('wood', 0x9A7650);
    const darkWood = V.material('wood', 0x6E5236);
    const iron = V.material('metal', 0x2E3134);
    const sack = V.material('fabric', 0xCDB98E);
    const add = (mesh, x, y, z, parent = c) => { mesh.position.set(x, y, z); mesh.castShadow = true; parent.add(mesh); return mesh; };
    // Horse: body, chest, neck, head, ears, mane and tail.
    add(transportMesh(new THREE.BoxGeometry(0.58, 0.66, 1.55), coat), 0, 1.3, 1.55);
    add(transportMesh(new THREE.BoxGeometry(0.54, 0.6, 0.3), coat), 0, 1.25, 2.38);
    const neck = add(transportMesh(new THREE.BoxGeometry(0.3, 0.85, 0.36), coat), 0, 1.78, 2.5);
    neck.rotation.x = 0.55;
    const head = add(transportMesh(new THREE.BoxGeometry(0.28, 0.3, 0.68), coat), 0, 2.12, 2.86);
    head.rotation.x = 0.5;
    [-0.09, 0.09].forEach(x => add(transportMesh(new THREE.BoxGeometry(0.06, 0.16, 0.06), coat), x, 2.36, 2.62));
    const crest = add(transportMesh(new THREE.BoxGeometry(0.1, 0.8, 0.12), mane), 0, 1.86, 2.33);
    crest.rotation.x = 0.55;
    const tail = add(transportMesh(new THREE.BoxGeometry(0.14, 0.72, 0.12), mane), 0, 1.12, 0.74);
    tail.rotation.x = -0.35;
    // Collar and the two shafts from the cart to the collar.
    add(transportMesh(new THREE.TorusGeometry(0.3, 0.07, 6, 12), darkWood), 0, 1.66, 2.3).rotation.x = 0.55;
    [-0.42, 0.42].forEach(x => add(transportMesh(new THREE.BoxGeometry(0.07, 0.07, 2.5), darkWood), x, 1.12, 1.15));
    // Legs pivot at the shoulder/hip (the gait swings rotation.x).
    const legs = [[-0.19, 2.12], [0.19, 2.12], [0.19, 1.0], [-0.19, 1.0]].map(([x, z]) => {
      const leg = new THREE.Group(); leg.position.set(x, 1.02, z); c.add(leg);
      add(transportMesh(new THREE.BoxGeometry(0.15, 0.92, 0.17), coat), 0, -0.46, 0, leg);
      add(transportMesh(new THREE.BoxGeometry(0.17, 0.12, 0.2), hoof), 0, -0.96, 0.02, leg);
      return leg;
    });
    // Cart: bed, side and end boards, two wheels on an axle.
    add(transportMesh(new THREE.BoxGeometry(1.36, 0.1, 2.3), wood), 0, 0.98, -1.35);
    [-0.66, 0.66].forEach(x => add(transportMesh(new THREE.BoxGeometry(0.06, 0.3, 2.3), darkWood), x, 1.18, -1.35));
    [-2.47, -0.23].forEach(z => add(transportMesh(new THREE.BoxGeometry(1.36, 0.3, 0.06), darkWood), 0, 1.18, z));
    add(transportMesh(new THREE.CylinderGeometry(0.05, 0.05, 1.7, 6).rotateZ(Math.PI / 2), iron), 0, 0.5, -1.45);
    const wheels = [-0.8, 0.8].map(x => {
      const wheel = add(transportMesh(new THREE.CylinderGeometry(0.5, 0.5, 0.1, 16).rotateZ(Math.PI / 2), darkWood), x, 0.5, -1.45);
      add(transportMesh(new THREE.TorusGeometry(0.47, 0.035, 5, 18).rotateY(Math.PI / 2), iron), 0, 0, 0, wheel);
      return wheel;
    });
    // Sacks of potatoes, as in the photo of 12.11.
    [[-0.34, -2.0], [0.34, -2.0], [-0.34, -1.35], [0.34, -1.35], [0, -1.65]].forEach(([x, z], i) => {
      const bag = add(transportMesh(new THREE.SphereGeometry(0.33, 8, 6), sack), x, i === 4 ? 1.62 : 1.3, z);
      bag.scale.set(1, 0.72, 1.15);
    });
    // The driver on the front board: coat, head and cap.
    add(transportMesh(new THREE.BoxGeometry(0.44, 0.58, 0.32), new THREE.MeshLambertMaterial({ color: 0x55606B })), 0.16, 1.45, -0.5);
    add(transportMesh(new THREE.SphereGeometry(0.14, 10, 8), new THREE.MeshLambertMaterial({ color: 0xE0B48E })), 0.16, 1.9, -0.48);
    add(transportMesh(new THREE.CylinderGeometry(0.15, 0.16, 0.1, 10), new THREE.MeshLambertMaterial({ color: 0xE8E4DA })), 0.16, 2.02, -0.48);
    c.userData.legs = legs;
    c.userData.wheels = wheels;
    return c;
  }

  // A diesel locomotive with a few freight wagons (ticket 2.16: the train
  // behind the closed barrier). Faces +Z, centred; about 58 m long.
  function createTrain(tailColor = 0x6B4A36) {
    const t = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const red = transportMaterial('locomotive', 0xC8312A);
    const grey = V.material('metal', 0x8C949A);
    const dark = transportMaterial('hvac', 0x25292D);
    const glass = V.material('glass', 0xffffff);
    const add = (mesh, x, y, z) => { mesh.position.set(x, y, z); mesh.castShadow = true; t.add(mesh); return mesh; };
    const bogies = (z0, length) => [z0 - length / 2 + 2.2, z0 + length / 2 - 2.2].forEach(z => {
      add(transportMesh(new THREE.BoxGeometry(2.6, 0.7, 2.8), transportMaterial('bogie', 0x25292D)), 0, 0.55, z);
    });
    // Locomotive at the head (+Z): long hood, cab with windows, stripe.
    const locoZ = 21.3, locoL = 16; // 1.2 m couplings; the whole train spans ±29.3 m
    add(transportMesh(new THREE.BoxGeometry(3.0, 2.9, locoL), red), 0, 2.45, locoZ);
    add(transportMesh(new THREE.BoxGeometry(3.04, 0.35, locoL), grey), 0, 1.35, locoZ);
    add(transportMesh(new THREE.BoxGeometry(3.1, 0.25, locoL + 0.2), dark), 0, 3.98, locoZ);
    add(transportMesh(new THREE.BoxGeometry(2.4, 0.9, 0.08), glass), 0, 3.15, locoZ + locoL / 2 + 0.01);
    [-1.51, 1.51].forEach(x => add(transportMesh(new THREE.BoxGeometry(0.06, 0.8, 1.6), glass), x, 3.1, locoZ + locoL / 2 - 1.3));
    bogies(locoZ, locoL);
    // Freight wagons: two box cars and a tank.
    const wagons = [[5.6, 0x7A4A32, 'box'], [-8.6, 0x3C4247, 'tank'], [-22.8, tailColor, 'box']];
    wagons.forEach(([z, color, kind]) => {
      const m = kind === 'tank' ? V.material('metal', color, V.tankMap()) : transportMaterial('wagon', color);
      if (kind === 'tank') {
        add(transportMesh(new THREE.CylinderGeometry(1.4, 1.4, 12.2, 14).rotateX(Math.PI / 2), m), 0, 2.4, z);
        add(transportMesh(new THREE.BoxGeometry(2.9, 0.3, 13), dark), 0, 1.0, z);
      } else {
        add(transportMesh(new THREE.BoxGeometry(2.9, 3.0, 13), m), 0, 2.5, z);
        add(transportMesh(new THREE.BoxGeometry(0.05, 2.2, 3.2), dark), 1.47, 2.4, z);
        add(transportMesh(new THREE.BoxGeometry(0.05, 2.2, 3.2), dark), -1.47, 2.4, z);
      }
      bogies(z, 13);
    });
    return t;
  }

  function createTruck(color = 0x3B82F6) {
    const truck = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const cabMat = transportMaterial('cab', color);
    const containerMat = transportMaterial('cargo', 0x64748B);
    const glassMat = V.material('glass', 0xffffff);
    const wheelMat = V.material('rubber', 0x18181B);

    // Driver Cab
    const cab = transportMesh(new THREE.BoxGeometry(2.1, 1.6, 2.0), cabMat);
    cab.position.set(0, 1.15, 1.8);
    cab.castShadow = true;
    truck.add(cab);

    // Cab windshield
    const wind = transportMesh(new THREE.BoxGeometry(2.0, 0.65, 0.1), glassMat);
    wind.position.set(0, 1.45, 2.81);
    truck.add(wind);
    truck.userData.lampSpec = { front: { x: 0.75, y: 0.85, z: 2.8 }, rear: { x: 0.8, y: 0.75, z: -3.6 } };

    // Cargo Box
    const cargo = transportMesh(new THREE.BoxGeometry(2.2, 2.1, 4.4), containerMat);
    cargo.position.set(0, 1.5, -1.4);
    cargo.castShadow = true;
    truck.add(cargo);

    // Chassis frame
    const chassis = transportMesh(new THREE.BoxGeometry(1.6, 0.28, 6.2), V.material('metal', 0x334155));
    chassis.position.set(0, 0.45, 0.1);
    truck.add(chassis);

    // Wheels
    const wheelGeo = new THREE.CylinderGeometry(0.42, 0.42, 0.3, 12);
    wheelGeo.rotateZ(Math.PI / 2);
    const wheels = [[-1.0, 0.42, 1.8], [1.0, 0.42, 1.8], [-1.0, 0.42, -1.0], [1.0, 0.42, -1.0], [-1.0, 0.42, -2.4], [1.0, 0.42, -2.4]].map(p => {
      const w = transportMesh(wheelGeo, wheelMat);
      w.position.set(p[0], p[1], p[2]);
      truck.add(w); return w;
    });
    // Cab lights, grille, mirrors and rims; a rear light bar on the box.
    const dark = V.material('metal', 0x23272C), chrome = V.material('steelRim', 0xC9D1D6);
    const put = (geo, mat, x, y, z) => { const m = transportMesh(geo, mat); m.position.set(x, y, z); truck.add(m); return m; };
    put(new THREE.BoxGeometry(1.4, 0.34, 0.05), V.material('grille', 0x23272C), 0, 0.95, 2.82);
    put(new THREE.BoxGeometry(2.2, 0.18, 0.2), dark, 0, 0.5, 2.85);
    [-1, 1].forEach(sx => {
      put(new THREE.BoxGeometry(0.34, 0.16, 0.06), V.material('lens', 0xFFF3CC), sx * 0.75, 0.85, 2.84);
      put(new THREE.BoxGeometry(0.3, 0.14, 0.06), V.material('lens', 0xD33D38), sx * 0.85, 0.75, -3.63);
      put(new THREE.BoxGeometry(0.1, 0.2, 0.22), dark, sx * 1.18, 1.55, 2.4);
      put(new THREE.BoxGeometry(0.02, 0.5, 1.2), V.material('glass', 0xffffff), sx * 1.06, 1.35, 1.7);
    });
    truck.userData.wheels = wheels; truck.userData.rims = [];
    wheels.forEach(w => { const rim = put(new THREE.CylinderGeometry(0.22, 0.22, 0.32, 8).rotateZ(Math.PI / 2), chrome, 0, 0, 0); rim.position.copy(w.position); truck.userData.rims.push(rim); });

    return truck;
  }

  function createTanker(color = '#FFFFFF') {
    const truck = createTruck(color), V = window.PDD_VEHICLE_MATERIALS;
    const cargo = truck.children.find(m => m.geometry?.type === 'BoxGeometry' && m.geometry.parameters.depth === 4.4);
    if (cargo) { truck.remove(cargo); cargo.geometry.dispose(); cargo.material.dispose(); }
    const tank = transportMesh(new THREE.CylinderGeometry(1.03,1.03,4.4,20),V.material('metal', 0xD97E32, V.tankMap()));
    tank.rotation.x = Math.PI/2; tank.position.set(0,1.5,-1.4); tank.castShadow=true;truck.add(tank);
    for (const z of [-2.9,.1]) { const band=transportMesh(new THREE.TorusGeometry(1.04,.035,6,20),V.material('metal', 0xE2DED4));band.position.set(0,1.5,z);truck.add(band); }
    const deck = modelBox(truck,[.6,.08,3.8],0x47535C,0,2.55,-1.4);
    deck.material = V.material('grille', 0x47535C);
    truck.userData.tanker=true;return truck;
  }

  function createMotorcycleSidecar(color) {
    const V=window.PDD_VEHICLE_MATERIALS,bike=createMotorcycle(color,0x46535C),g=new THREE.Group();bike.position.x=.46;g.add(bike);
    Object.assign(g.userData,bike.userData);g.userData.sidecar=true;
    const paint=V.material('paint',0x46535C),seat=V.material('leather',0x252B31),metal=V.material('metal',0xB8C0C6);
    const add=(m,x=0,y=0,z=0)=>{m.position.set(x,y,z);m.castShadow=true;g.add(m);return m;};
    const box=(size,mat,x,y,z)=>add(transportMesh(new THREE.BoxGeometry(...size),mat),x,y,z);
    // Boat-shaped tub: tapered nose, opening with an actual inset seat,
    // connected axle, suspension and a fender over the third wheel.
    const shell=transportProfile([[-.78,.30],[.63,.30],[.85,.45],[.71,.65],[.29,.75],[.24,.51],[-.72,.51]],.76,paint,.06);add(shell,-.52);
    for(const side of [-1,1])add(transportProfile([[-.75,.45],[.27,.45],[.27,.75],[-.75,.73]],.06,paint,.01),-.52+side*.36);
    box([.76,.24,.06],paint,-.52,.60,-.735);
    box([.54,.055,.57],seat,-.52,.58,-.27);
    box([.54,.25,.065],seat,-.52,.74,-.58);
    add(transportGlassQuad([[-.83,.754,.23],[-.21,.754,.23],[-.25,.93,.11],[-.79,.93,.11]],V.material('glass',0x8497A3)));
    box([.65,.025,.035],metal,-.52,.75,.23);
    for(const side of [-1,1])box([.045,.025,.38],metal,-.52+side*.375,.755,-.14);
    const points=[];
    for(let i=0;i<=10;i++){const a=.12*Math.PI+i*.76*Math.PI/10;points.push([-.20+.395*Math.cos(a),.345+.395*Math.sin(a)]);}
    for(let i=10;i>=0;i--){const a=.12*Math.PI+i*.76*Math.PI/10;points.push([-.20+.355*Math.cos(a),.345+.355*Math.sin(a)]);}
    add(transportProfile(points,.18,paint,0),-1.00);
    const wheel=add(transportMesh(new THREE.TorusGeometry(.28,.065,8,20).rotateY(Math.PI/2),V.material('rubberRound',0x151719)),-1,.345,-.20);
    const rim=transportMesh(new THREE.CylinderGeometry(.215,.215,.025,16).rotateZ(Math.PI/2),V.material('steelRim',0xC9D1D6));rim.position.x=-.078;wheel.add(rim);
    box([1.40,.07,.075],metal,-.28,.36,-.20);
    box([.95,.07,.075],metal,-.02,.44,.23);
    g.userData.wheels=[...bike.userData.wheels,wheel];g.userData.modelVersion=2;
    mergeTransportParts(g);
    return g;
  }


  function createBusShelter() {
    const g=new THREE.Group();g.userData.busShelter=true;
    const glass=new THREE.MeshLambertMaterial({color:0xB3CDD5,transparent:true,opacity:.6,side:THREE.DoubleSide});
    for(const z of [-2,2])modelBox(g,[.08,2.7,.08],0x4D6672,-.9,1.35,z);
    modelBox(g,[2.2,.16,4.5],0x496E7E,0,2.75,0);
    const back=new THREE.Mesh(new THREE.BoxGeometry(.04,2.3,4),glass);back.position.set(-.95,1.35,0);g.add(back);
    modelBox(g,[.55,.12,3.3],0xB08B5F,-.45,.65,0);
    for(const z of [-1.3,1.3])modelBox(g,[.08,.65,.08],0x4D6672,-.45,.325,z);
    return g;
  }

  // --- Special / Police Car Model Factory ---
  function createSpecialCar(color = 0xFFFFFF) {
    const car = window.PDD_VEHICLES.create('sedan', color), V = window.PDD_VEHICLE_MATERIALS;
    // Blue side stripe along the doors.
    const stripeMat = V.material('paint', 0x0574F8);
    const s1 = transportMesh(new THREE.BoxGeometry(0.03, 0.18, 3.0), stripeMat);
    s1.position.set(-0.915, 0.62, 0);
    const s2 = transportMesh(new THREE.BoxGeometry(0.03, 0.18, 3.0), stripeMat);
    s2.position.set(0.915, 0.62, 0);
    car.add(s1);
    car.add(s2);

    // Flashing light bar on roof
    const bar = new THREE.Group();
    bar.position.set(0, car.userData.height + 0.04, -0.2); // on the roof
    const mount = transportMesh(new THREE.BoxGeometry(0.8, 0.08, 0.2), V.material('metal', 0x1E293B));
    bar.add(mount);

    const blueBeacon = transportMesh(new THREE.BoxGeometry(0.35, 0.16, 0.18), V.material('lens', 0x0574F8));
    blueBeacon.position.set(-0.2, 0.1, 0);
    const redBeacon = transportMesh(new THREE.BoxGeometry(0.35, 0.16, 0.18), V.material('lens', 0xEF4444));
    redBeacon.position.set(0.2, 0.1, 0);
    bar.add(blueBeacon);
    bar.add(redBeacon);
    car.add(bar);
    car.userData.beacons = [blueBeacon, redBeacon];
    window.PDD_VEHICLES.addGlow(blueBeacon, 0x208CFF, 1.7);
    window.PDD_VEHICLES.addGlow(redBeacon, 0xFF3434, 1.7);

    return car;
  }

  // --- Motorcycle Model Factory ---
  // A road bike with its rider: tank, seat, engine, exhaust, fork, fenders,
  // lamps and spoked wheels. Paint varies from bike to bike (the badge keeps
  // the scenario colour, so the legend still matches).
  const MOTO_PAINTS = [0xD62D2D, 0x1F2933, 0x2563EB, 0xF1F3F5, 0xF08A24, 0x2F855A, 0xE8C547, 0x9AA5B1, 0x7A5BC6];
  function createMotorcycle(color = 0xF59E0B, paint = MOTO_PAINTS[Math.floor(Math.random() * MOTO_PAINTS.length)]) {
    const moto=new THREE.Group(),V=window.PDD_VEHICLE_MATERIALS,look=personLook(Math.floor(Math.random()*12));
    const paintMat=V.material('paint',paint),metal=V.material('metal',0xB8C0C6),dark=V.material('metal',0x23272C);
    const tyre=V.material('rubberRound',0x151719),seat=V.material('leather',0x23272C);
    const add=(m,x=0,y=0,z=0,parent=moto)=>{m.position.set(x,y,z);m.castShadow=true;parent.add(m);return m;};
    const box=(size,mat,x,y,z,parent=moto)=>add(transportMesh(new THREE.BoxGeometry(...size),mat),x,y,z,parent);
    const bar=(a,b,r,mat,parent=moto)=>{
      const p=new THREE.Vector3(...a),q=new THREE.Vector3(...b),m=transportMesh(new THREE.CylinderGeometry(r,r,p.distanceTo(q),8),mat);
      m.position.copy(p.clone().add(q).multiplyScalar(.5));m.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),q.sub(p).normalize());m.castShadow=true;parent.add(m);return m;
    };
    moto.userData.wheels=[];
    for(const z of [.74,-.72]) {
      const w=add(new THREE.Group(),0,.345,z);moto.userData.wheels.push(w);
      add(transportMesh(new THREE.TorusGeometry(.28,.065,8,20).rotateY(Math.PI/2),tyre),0,0,0,w);
      const wheelParts=[];
      const wheelPart=m=>{wheelParts.push(m);return m;};
      wheelPart(transportMesh(new THREE.TorusGeometry(.232,.022,5,20).rotateY(Math.PI/2),metal));
      wheelPart(transportMesh(new THREE.CylinderGeometry(.065,.065,.15,10).rotateZ(Math.PI/2),metal));
      for(let i=0;i<4;i++){const spoke=transportMesh(new THREE.BoxGeometry(.027,.455,.022),metal);spoke.rotation.x=i*Math.PI/4;wheelPart(spoke);}
      const hub=mergeStatic(wheelParts,metal);w.add(hub);wheelParts.forEach(m=>m.geometry.dispose());
      // A close-fitting curved fender instead of a flat board above the tyre.
      const fender=[];
      for(let i=0;i<=10;i++){const a=.20*Math.PI+i*.60*Math.PI/10;fender.push([z+.39*Math.cos(a),.345+.39*Math.sin(a)]);}
      for(let i=10;i>=0;i--){const a=.20*Math.PI+i*.60*Math.PI/10;fender.push([z+.35*Math.cos(a),.345+.35*Math.sin(a)]);}
      add(transportProfile(fender,.16,paintMat,0));
    }
    // Tubular chassis, swingarm, engine cooling fins and a rounded fuel tank.
    for(const side of [-1,1]) {
      bar([side*.10,.40,-.62],[side*.10,.64,.24],.028,dark);
      bar([side*.10,.64,.24],[side*.10,.86,-.47],.028,dark);
      bar([side*.10,.86,-.47],[side*.10,.40,-.62],.028,dark);
      bar([side*.10,.345,-.72],[side*.10,.55,-.09],.03,metal);
    }
    box([.34,.24,.38],V.material('grille',0x30363B),0,.52,.04);
    const crank=add(transportMesh(new THREE.CylinderGeometry(.13,.13,.34,12).rotateZ(Math.PI/2),metal),0,.45,.05);
    add(transportProfile([[-.09,.70],[.43,.70],[.48,.86],[.31,1.00],[.00,.99],[-.16,.89]],.37,paintMat,.035));
    add(transportProfile([[-.81,.84],[-.19,.84],[-.19,.93],[-.46,.96],[-.77,.94]],.31,seat,.015));
    box([.31,.055,.18],paintMat,0,.825,-.77);
    bar([.19,.45,.06],[.21,.37,-.43],.033,metal);
    bar([.21,.37,-.43],[.21,.43,-.86],.065,metal);
    // Front fork and headlight are supported by the steering head.
    for(const side of [-1,1])bar([side*.09,.345,.74],[side*.09,1.015,.45],.028,metal);
    box([.25,.06,.09],dark,0,.98,.46);
    bar([-.30,1.10,.60],[.30,1.10,.60],.022,dark);
    bar([0,1.02,.46],[0,1.10,.60],.025,metal);
    for(const side of [-1,1])bar([side*.23,1.10,.60],[side*.33,1.10,.60],.032,tyre);
    add(transportMesh(new THREE.CylinderGeometry(.10,.10,.085,14).rotateX(Math.PI/2),dark),0,.90,.76);
    add(transportMesh(new THREE.CylinderGeometry(.083,.083,.02,14).rotateX(Math.PI/2),V.material('lens',0xFFF3CC)),0,.90,.814);
    box([.14,.065,.04],V.material('lens',0xD33D38),0,.85,-.887);
    for(const side of [-1,1])bar([side*.15,.46,-.10],[side*.26,.46,-.10],.023,metal);
    // Anatomical riding pose: elbows and knees bent, both hands on grips,
    // feet on the pegs and the pelvis actually resting on the seat.
    const jacket=sceneryMat(look.top),pants=sceneryMat(look.pants),skin=sceneryMat(look.skin);
    const rider=add(new THREE.Group());moto.userData.rider=rider;
    const torso=add(transportProfile([[-.40,1.02],[-.11,1.00],[.07,1.39],[-.18,1.43]],.34,jacket,.02),0,0,0,rider);
    for(const side of [-1,1]) {
      bar([side*.17,1.36,-.01],[side*.26,1.22,.22],.065,jacket,rider);
      bar([side*.26,1.22,.22],[side*.295,1.105,.60],.054,jacket,rider);
      add(transportMesh(new THREE.SphereGeometry(.052,8,5),skin),side*.295,1.105,.60,rider).name='rider-hand';
      bar([side*.15,1.045,-.32],[side*.19,.88,.23],.078,pants,rider);
      bar([side*.19,.88,.23],[side*.215,.515,-.09],.065,pants,rider);
      box([.13,.09,.23],seat,side*.215,.475,-.035,rider);
    }
    bar([0,1.37,.01],[0,1.52,.06],.067,skin,rider);
    const helmet=add(transportMesh(new THREE.SphereGeometry(.175,16,10),paintMat),0,1.59,.075,rider);helmet.scale.set(1,1.05,1.08);
    // Curved visor lies on the shell, rather than a box across the face.
    const visor=transportMesh(new THREE.SphereGeometry(.180,16,5,Math.PI*.29,Math.PI*.42,Math.PI*.36,Math.PI*.31),V.material('glass',0x708592));
    visor.scale.set(1,1.05,1.08);add(visor,0,1.59,.075,rider);
    moto.userData.paint=paint;moto.userData.modelVersion=2;
    moto.userData.lampSpec={front:{x:0,y:.90,z:.83},rear:{x:0,y:.85,z:-.91},single:true};
    mergeTransportParts(rider); mergeTransportParts(moto);
    return moto;
  }


  // Procedural appearances: no texture downloads or extra image assets.
  const PEOPLE_COLORS = [0x3979A3, 0xB6654F, 0x66845A, 0xD5AA49, 0x865E94, 0xD4C8B3];
  function personLook(variant) {
    return {
      variant,
      skin: [0xE9AF83, 0xC58C65, 0xF2C9A5, 0x986647][variant % 4],
      hair: [0x49372B, 0xB68A4E, 0x392D2B, 0xB4ACA1][Math.floor(variant / 3) % 4],
      pants: [0x344759, 0x55544E, 0x37473B, 0x655066][variant % 4],
      top: PEOPLE_COLORS[variant % PEOPLE_COLORS.length],
    };
  }
  function modelPart(group, geometry, color, x, y, z) {
    const mesh = new THREE.Mesh(geometry, sceneryMat(color));
    mesh.position.set(x, y, z); mesh.castShadow = true; group.add(mesh);
    return mesh;
  }
  function modelBox(group, size, color, x, y, z) {
    return modelPart(group, new THREE.BoxGeometry(...size), color, x, y, z);
  }
  function modelBar(group, start, end, width, color) {
    const a = new THREE.Vector3(...start), b = new THREE.Vector3(...end);
    const mesh = modelBox(group, [width, a.distanceTo(b), width], color, ...a.clone().add(b).multiplyScalar(0.5).toArray());
    mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), b.sub(a).normalize());
    return mesh;
  }
  function mergeModelParts(group, doubleSided = false) {
    // Bake colours into vertices: one draw call for each independently animated
    // part, even when it contains shoes, hands, a face, hair and accessories.
    const parts = group.children.filter(o => o.isMesh);
    if (!parts.length) return;
    const colors = [];
    parts.forEach(part => {
      const count = part.geometry.index?.count || part.geometry.attributes.position.count;
      const c = part.material.color;
      for (let i = 0; i < count; i++) colors.push(c.r, c.g, c.b);
    });
    const mesh = mergeStatic(parts, new THREE.MeshLambertMaterial({ vertexColors: true, side: doubleSided ? THREE.DoubleSide : THREE.FrontSide }));
    mesh.geometry.setAttribute('color', new THREE.Float32BufferAttribute(colors, 3));
    mesh.castShadow = true;
    parts.forEach(part => { group.remove(part); part.geometry.dispose(); part.material.dispose(); });
    group.add(mesh);
  }

  // --- Cyclist Model Factory ---
  function createCyclist(color = 0x10B981, variant = Math.floor(Math.random() * 12)) {
    const bike = new THREE.Group(), rider = new THREE.Group(), V = window.PDD_VEHICLE_MATERIALS;
    const look = personLook(variant), style = variant % 3;
    bike.add(rider); bike.userData.rider = rider;
    bike.userData.wheels = [];
    const dark = 0x303942, tyre = 0x23282D;
    // Open low-poly rims and spokes have the same triangle count as solid tyres.
    [0.65, -0.65].forEach(z => {
      const wheel = new THREE.Group(); wheel.position.set(0, 0.36, z);
      const ring = modelPart(wheel, new THREE.RingGeometry(0.31, 0.36, 12), tyre, 0, 0, 0);
      ring.rotation.y = Math.PI / 2;
      modelBox(wheel, [0.045, 0.63, 0.025], 0x9AA7AD, 0, 0, 0);
      modelBox(wheel, [0.045, 0.025, 0.63], 0x9AA7AD, 0, 0, 0);
      mergeModelParts(wheel, true);
      const surface = V.material('metal', 0xffffff); surface.vertexColors = true; surface.side = THREE.DoubleSide;
      wheel.children[0].material.dispose(); wheel.children[0].material = surface;
      bike.add(wheel); bike.userData.wheels.push(wheel);
    });
    const rear = [0, 0.36, -0.65], crank = [0, 0.48, -0.06];
    const saddle = [0, 0.83, -0.25], fork = [0, 0.84, 0.45];
    [[rear, crank], [rear, saddle], [saddle, crank], [crank, fork],
      [style === 0 ? crank : saddle, fork], [fork, [0, 0.36, 0.65]]].forEach(([a, b]) => modelBar(bike, a, b, 0.055, color));
    modelBox(bike, [0.24, 0.07, 0.3], dark, 0, 0.85, -0.27);
    modelBar(bike, fork, [0, 1.01, 0.48], 0.045, dark);
    modelBox(bike, [0.48, 0.045, 0.06], dark, 0, 1.01, 0.48);
    if (style === 0) modelBox(bike, [0.4, 0.24, 0.28], 0xB59C70, 0, 0.91, 0.66);
    if (style === 2) modelBox(bike, [0.32, 0.3, 0.32], look.pants, 0.16, 0.58, -0.65);

    const torso = modelBox(rider, [0.3, 0.44, 0.25], look.top, 0, 1.06, -0.15);
    torso.rotation.x = 0.24 + style * 0.08;
    modelPart(rider, new THREE.SphereGeometry(0.15, 8, 6), look.skin, 0, 1.38, -0.05);
    modelPart(rider, new THREE.SphereGeometry(0.18, 8, 4, 0, Math.PI * 2, 0, Math.PI / 2), style === 1 ? 0xE8E2CF : color, 0, 1.4, -0.05);
    modelBox(rider, [0.09, 0.035, 0.27], dark, 0, 1.565, -0.05);
    if (style === 2) modelBox(rider, [0.25, 0.33, 0.14], 0xD6AA50, 0, 1.04, -0.34);
    [-1, 1].forEach(side => {
      modelBar(rider, [side * 0.18, 1.2, -0.07], [side * 0.2, 1.02, 0.47], 0.09, look.top);
      modelBox(rider, [0.085, 0.08, 0.1], look.skin, side * 0.2, 1.02, 0.47);
      modelBar(rider, [side * 0.13, 0.87, -0.2], [side * 0.13, 0.65, 0.15], 0.12, look.pants);
      modelBar(rider, [side * 0.13, 0.65, 0.15], [side * 0.13, 0.34, -0.04], 0.1, look.pants);
    });
    const pedals = new THREE.Group(); pedals.position.set(0, 0.48, -0.06);
    [-1, 1].forEach(side => {
      modelBox(pedals, [0.07, 0.28, 0.06], dark, side * 0.16, side * 0.1, 0);
      modelBox(pedals, [0.18, 0.05, 0.08], dark, side * 0.19, side * 0.24, 0);
    });
    mergeModelParts(pedals); bike.add(pedals); bike.userData.pedals = pedals;
    mergeModelParts(rider); mergeModelParts(bike);
    // Keep the existing vertex colours and one draw call for the frame.
    const frame = bike.children.find(o => o.isMesh);
    const surface = V.material('paint', 0xffffff); surface.vertexColors = true;
    frame.material.dispose(); frame.material = surface;
    bike.userData.appearance = variant;
    return bike;
  }

  // --- Pedestrian Model Factory ---
  function createPedestrian(color = 0x0574F8, variant = Math.floor(Math.random() * 12)) {
    const ped = new THREE.Group(), look = personLook(variant);
    ped.userData.arms = []; ped.userData.legs = [];
    [-1, 1].forEach(side => {
      const hip = new THREE.Group(); hip.position.set(side * 0.11, 0.65, 0);
      modelBox(hip, [0.15, 0.6, 0.16], look.pants, 0, -0.3, 0);
      modelBox(hip, [0.17, 0.09, 0.25], 0xECE5D6, 0, -0.61, 0.035);
      mergeModelParts(hip); ped.add(hip); ped.userData.legs.push(hip);
      const arm = new THREE.Group(); arm.position.set(side * 0.27, 1.12, 0);
      arm.rotation.z = side * 0.1;
      modelBox(arm, [0.13, 0.38, 0.14], color, 0, -0.16, 0);
      modelBox(arm, [0.12, 0.12, 0.13], look.skin, 0, -0.4, 0);
      mergeModelParts(arm); ped.add(arm); ped.userData.arms.push(arm);
    });
    modelBox(ped, [0.42, 0.58, 0.26], color, 0, 0.92, 0);
    modelPart(ped, new THREE.SphereGeometry(0.18, 8, 6), look.skin, 0, 1.36, 0);
    const hat = variant % 3;
    modelPart(ped, new THREE.SphereGeometry(0.185, 8, 4, 0, Math.PI * 2, 0, Math.PI / 2),
      hat === 0 ? look.top : look.hair, 0, 1.39, 0);
    if (hat === 0) modelBox(ped, [0.25, 0.04, 0.18], look.top, 0, 1.42, 0.14);
    if (hat === 2) modelBox(ped, [0.3, 0.25, 0.09], look.hair, 0, 1.28, -0.14);
    if (variant % 2) modelBox(ped, [0.3, 0.4, 0.16], look.top, 0, 0.95, -0.19);
    mergeModelParts(ped);
    const height = [0.94, 1.04, 1, 1.09][variant % 4];
    ped.scale.set(variant % 3 === 1 ? 1.08 : 1, height, 1);
    ped.userData.appearance = variant;
    return ped;
  }

  // --- Russian Road Sign Factory (GOST 52290) ---
  // Sign faces must sit fully in front of the thickest support. Keeping this
  // shared offset for both the main sign and supplementary plates prevents a
  // pole from showing through their artwork at any camera distance.
  const ROAD_SIGN_FACE_Z = -0.09;
  // Signs are drawn larger than life (~1.3×) so they read on a phone screen.
  const SIGN_FACE = 2.1;
  function createRoadSign(code, poleHeight = 3.6) {
    const group = new THREE.Group();
    const pole = new THREE.Mesh(
      new THREE.CylinderGeometry(0.045, 0.055, poleHeight, 8),
      new THREE.MeshLambertMaterial({ color: 0x697477 })
    );
    pole.position.y = poleHeight / 2;
    pole.castShadow = true;
    group.add(pole);
    let texture = signTextureCache.get(code);
    if (!texture && window.PDD_SIGN_TEXTURES && window.PDD_SIGN_TEXTURES[code]) {
      texture = new THREE.TextureLoader().load(window.PDD_SIGN_TEXTURES[code]);
      texture.anisotropy = Math.min(4, renderer.capabilities.getMaxAnisotropy());
      signTextureCache.set(code, texture);
    }
    // A transparent exact SVG face, no nested coplanar coloured primitives.
    const aspect = (window.PDD_SIGN_ASPECT || {})[code];
    const face = new THREE.Mesh(
      aspect ? new THREE.PlaneGeometry(aspect > 2 ? 2.9 : 1.8 * aspect, aspect > 2 ? 2.9 / aspect : 1.8) : new THREE.PlaneGeometry(SIGN_FACE, SIGN_FACE),
      new THREE.MeshBasicMaterial({ map: texture, transparent: true, alphaTest: 0.12 })
    );
    face.position.set(0, poleHeight - 0.35, ROAD_SIGN_FACE_Z);
    face.rotation.y = Math.PI;
    group.add(face);
    addSignBack(face);
    return group;
  }

  // The back of a sign: plain grey metal in the sign's outline, so a sign
  // meant for the other direction shows nothing readable.
  const signBackMaterials = new Map();
  function signBackMaterial(texture) {
    let material = signBackMaterials.get(texture);
    if (!material) {
      material = new THREE.MeshLambertMaterial({ color: 0x8E979C, map: texture, transparent: true, alphaTest: 0.12 });
      material.onBeforeCompile = shader => {
        shader.fragmentShader = shader.fragmentShader.replace('#include <map_fragment>',
          'diffuseColor.a *= texture2D( map, vUv ).a;');
      };
      signBackMaterials.set(texture, material);
    }
    return material;
  }

  // A material copy for clipping. Material.clone() drops onBeforeCompile:
  // a sign's back cut at a seam used to show the sign itself through its grey.
  function cloneMaterial(material) {
    const copy = material.clone();
    copy.onBeforeCompile = material.onBeforeCompile;
    return copy;
  }

  function addSignBack(face) {
    const back = new THREE.Mesh(face.geometry, signBackMaterial(face.material.map));
    back.position.copy(face.position); back.position.z += 0.02;
    back.rotation.y = face.rotation.y + Math.PI;
    back.userData.signBack = true;
    face.userData.back = back;
    face.parent.add(back);
    return back;
  }

  function createTriangleMesh(size, depth, color) {
    const shape = new THREE.Shape();
    const h = size * Math.sqrt(3) / 2;
    shape.moveTo(-size / 2, -h / 3);
    shape.lineTo(size / 2, -h / 3);
    shape.lineTo(0, 2 * h / 3);
    shape.closePath();

    const geom = new THREE.ExtrudeGeometry(shape, { depth, bevelEnabled: false });
    return new THREE.Mesh(geom, new THREE.MeshBasicMaterial({ color }));
  }

  // --- Working Traffic Light Factory ---
  function createPriorityPlate(mainRoad = ['south', 'north'], branches = ['north','south','west','east']) {
    const canvas = document.createElement('canvas');
    canvas.width = 480; canvas.height = 360;
    const ctx = canvas.getContext('2d');
    ctx.scale(2, 2); // drawn in 240×180 units, twice the pixels for sharpness
    ctx.fillStyle = '#fafafa'; ctx.fillRect(0, 0, 240, 180);
    ctx.strokeStyle = '#20252a'; ctx.lineWidth = 8; ctx.strokeRect(5, 5, 230, 170);
    const ends = { north: [120, 25], south: [120, 155], west: [30, 90], east: [210, 90], northEast: [184,25] };
    branches.forEach(direction => {
      ctx.lineWidth = mainRoad.includes(direction) ? 24 : 6;
      ctx.beginPath(); ctx.moveTo(120, 90); ctx.lineTo(...ends[direction]); ctx.stroke();
    });
    const face = new THREE.Mesh(new THREE.PlaneGeometry(1.5, 1.13),
      new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(canvas) }));
    // In front of the pole, like every sign face: the pole must not cross it.
    face.position.z = ROAD_SIGN_FACE_Z;
    face.rotation.y = Math.PI;
    const group = new THREE.Group(); group.add(face);
    addSignBack(face);
    return group;
  }

  // --- Traffic Controller Factory (Регулировщик, ГОСТ / ПДД 6.10) ---
  function createTrafficController(pose = 'arms_down', orientation = 'front') {
    const group = new THREE.Group();
    group.userData.isRegulator = true;
    group.userData.pose = pose;
    group.userData.orientation = orientation;

    const darkUniform = new THREE.MeshLambertMaterial({ color: 0x1E293B });
    const vestLime = new THREE.MeshLambertMaterial({ color: 0x84CC16 });
    const stripeSilver = new THREE.MeshLambertMaterial({ color: 0xF1F5F9 });
    const skinMat = new THREE.MeshLambertMaterial({ color: 0xE2A76F });
    const capMat = new THREE.MeshLambertMaterial({ color: 0x0F172A });
    const whiteMat = new THREE.MeshLambertMaterial({ color: 0xFFFFFF });
    const blackMat = new THREE.MeshLambertMaterial({ color: 0x111827 });

    // Boots
    [-0.14, 0.14].forEach(x => {
      const boot = new THREE.Mesh(new THREE.BoxGeometry(0.18, 0.16, 0.32), blackMat);
      boot.position.set(x, 0.08, 0.04);
      group.add(boot);
    });

    // Legs
    [-0.14, 0.14].forEach(x => {
      const leg = new THREE.Mesh(new THREE.CylinderGeometry(0.1, 0.11, 0.85, 8), darkUniform);
      leg.position.set(x, 0.58, 0);
      group.add(leg);
    });

    // Torso with vest
    const torso = new THREE.Mesh(new THREE.BoxGeometry(0.5, 0.65, 0.3), vestLime);
    torso.position.set(0, 1.28, 0);
    group.add(torso);

    // Reflective stripes on vest
    const hStripe = new THREE.Mesh(new THREE.BoxGeometry(0.52, 0.08, 0.32), stripeSilver);
    hStripe.position.set(0, 1.18, 0);
    group.add(hStripe);

    [-0.15, 0.15].forEach(x => {
      const vStripe = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.45, 0.32), stripeSilver);
      vStripe.position.set(x, 1.38, 0);
      group.add(vStripe);
    });

    // Head
    const head = new THREE.Mesh(new THREE.BoxGeometry(0.24, 0.26, 0.24), skinMat);
    head.position.set(0, 1.73, 0);
    group.add(head);

    // Police Cap
    const capBand = new THREE.Mesh(new THREE.CylinderGeometry(0.15, 0.15, 0.08, 12), capMat);
    capBand.position.set(0, 1.86, 0);
    group.add(capBand);
    const capCrown = new THREE.Mesh(new THREE.CylinderGeometry(0.18, 0.15, 0.06, 12), capMat);
    capCrown.position.set(0, 1.92, 0);
    group.add(capCrown);
    const visor = new THREE.Mesh(new THREE.BoxGeometry(0.22, 0.02, 0.14), blackMat);
    visor.position.set(0, 1.84, 0.18);
    visor.rotation.x = 0.2;
    group.add(visor);
    const cockade = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.05, 0.02), new THREE.MeshLambertMaterial({ color: 0xF59E0B }));
    cockade.position.set(0, 1.88, 0.15);
    group.add(cockade);

    function createBaton() {
      const batonGroup = new THREE.Group();
      const bWhite = new THREE.Mesh(new THREE.CylinderGeometry(0.022, 0.022, 0.44, 8), whiteMat);
      batonGroup.add(bWhite);
      for (let i = -1; i <= 1; i++) {
        const stripe = new THREE.Mesh(new THREE.CylinderGeometry(0.023, 0.023, 0.07, 8), blackMat);
        stripe.position.y = i * 0.12;
        batonGroup.add(stripe);
      }
      return batonGroup;
    }

    // He faces +Z, so his right hand is on -X (6.10 is about the RIGHT arm:
    // a mirrored figure turns «left side, right arm forward» into a
    // prohibiting right side).
    const RX = -1;
    if (pose === 'right_arm_forward') {
      const rArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.12, 0.65), darkUniform);
      rArm.position.set(RX * 0.32, 1.45, 0.32);
      group.add(rArm);
      const rHand = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.08, 0.08), skinMat);
      rHand.position.set(RX * 0.32, 1.45, 0.66);
      group.add(rHand);
      const baton = createBaton();
      baton.rotation.x = Math.PI / 2;
      baton.position.set(RX * 0.32, 1.45, 0.88);
      group.add(baton);

      const lArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.55, 0.12), darkUniform);
      lArm.position.set(-RX * 0.32, 1.25, 0);
      group.add(lArm);
    } else if (pose === 'arm_up') {
      const rArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.65, 0.12), darkUniform);
      rArm.position.set(RX * 0.32, 1.8, 0);
      group.add(rArm);
      const rHand = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.08, 0.08), skinMat);
      rHand.position.set(RX * 0.32, 2.15, 0);
      group.add(rHand);
      const baton = createBaton();
      baton.position.set(RX * 0.32, 2.4, 0);
      group.add(baton);

      const lArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.55, 0.12), darkUniform);
      lArm.position.set(-RX * 0.32, 1.25, 0);
      group.add(lArm);
    } else {
      const lArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.55, 0.12), darkUniform);
      lArm.position.set(-RX * 0.32, 1.25, 0);
      group.add(lArm);

      const rArm = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.55, 0.12), darkUniform);
      rArm.position.set(RX * 0.32, 1.25, 0);
      group.add(rArm);
      const rHand = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.08, 0.08), skinMat);
      rHand.position.set(RX * 0.32, 0.94, 0);
      group.add(rHand);
      const baton = createBaton();
      baton.rotation.z = -0.3 * RX;
      baton.position.set(RX * 0.36, 0.8, 0);
      group.add(baton);
    }

    // Which side of him the player sees. The junction factory frame is
    // mirrored when the segment is registered (x and rotation.y flip), so
    // facing the player's left (his left side towards the player) is -π/2
    // here and becomes +π/2 in the world.
    if (orientation === 'facing_player' || orientation === 'front') group.rotation.y = Math.PI;
    else if (orientation === 'back') group.rotation.y = 0;
    else if (orientation === 'left_side') group.rotation.y = -Math.PI / 2;
    else if (orientation === 'right_side') group.rotation.y = Math.PI / 2;

    const pedestal = new THREE.Mesh(
      new THREE.CylinderGeometry(1.2, 1.3, 0.06, 24),
      new THREE.MeshLambertMaterial({ color: 0xE2E8F0 })
    );
    pedestal.position.y = 0.03;
    pedestal.receiveShadow = true;
    pedestal.visible = false; // Controller stands directly on the carriageway.
    group.add(pedestal);

    return group;
  }

  function createTrafficCone() {
    const group = new THREE.Group();
    const base = new THREE.Mesh(new THREE.BoxGeometry(0.38, 0.04, 0.38), new THREE.MeshLambertMaterial({ color: 0x1E293B }));
    base.position.y = 0.02;
    group.add(base);
    const body = new THREE.Mesh(new THREE.CylinderGeometry(0.04, 0.16, 0.62, 12), new THREE.MeshLambertMaterial({ color: 0xEA580C }));
    body.position.y = 0.33;
    group.add(body);
    const stripe = new THREE.Mesh(new THREE.CylinderGeometry(0.08, 0.11, 0.14, 12), new THREE.MeshLambertMaterial({ color: 0xFFFFFF }));
    stripe.position.y = 0.35;
    group.add(stripe);
    return group;
  }

  // Three separate parts (two trestles and the striped board) so that a car
  // driving into it breaks it apart instead of passing through.
  function createRoadworksBarrier(width = 2.4) {
    const group = new THREE.Group();
    const wood = new THREE.MeshLambertMaterial({ color: 0xE2E8F0 });
    const red = new THREE.MeshLambertMaterial({ color: 0xDC2626 });
    group.userData.parts = [];
    [-width / 2 + 0.2, width / 2 - 0.2].forEach(x => {
      const trestle = new THREE.Group();
      trestle.position.set(x, 0, 0);
      const leg = new THREE.Mesh(new THREE.BoxGeometry(0.08, 1.0, 0.08), wood);
      leg.position.set(0, 0.5, 0);
      trestle.add(leg);
      const foot = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.06, 0.6), wood);
      foot.position.set(0, 0.03, 0);
      trestle.add(foot);
      group.add(trestle); group.userData.parts.push(trestle);
    });
    const board = new THREE.Group();
    board.position.set(0, 0.72, 0);
    board.add(new THREE.Mesh(new THREE.BoxGeometry(width, 0.28, 0.04), wood));
    for (let x = -width / 2 + 0.3; x < width / 2; x += 0.5) {
      const s = new THREE.Mesh(new THREE.BoxGeometry(0.18, 0.28, 0.042), red);
      s.position.set(x, 0, 0);
      s.rotation.z = 0.4;
      board.add(s);
    }
    group.add(board); group.userData.parts.push(board);
    return group;
  }

  function createEmergencyTriangle() {
    const group = new THREE.Group();
    // About twice life size: seen from above a real one is a speck.
    group.scale.setScalar(2.2);
    const shape = new THREE.Shape();
    const h = 0.45 * Math.sqrt(3) / 2;
    shape.moveTo(-0.22, 0); shape.lineTo(0.22, 0); shape.lineTo(0, h); shape.closePath();
    const hole = new THREE.Path();
    const h2 = 0.3 * Math.sqrt(3) / 2;
    hole.moveTo(-0.15, 0.04); hole.lineTo(0.15, 0.04); hole.lineTo(0, 0.04 + h2); hole.closePath();
    shape.holes.push(hole);
    const geom = new THREE.ShapeGeometry(shape);
    const mesh = new THREE.Mesh(geom, new THREE.MeshBasicMaterial({ color: 0xEF4444, side: THREE.DoubleSide }));
    mesh.position.y = 0.02;
    mesh.rotation.x = -0.15;
    group.add(mesh);
    const stand = new THREE.Mesh(new THREE.BoxGeometry(0.44, 0.02, 0.15), new THREE.MeshLambertMaterial({ color: 0x475569 }));
    stand.position.y = 0.01;
    group.add(stand);
    return group;
  }

  function createTrafficLight(initialState = 'red', arrow = null) {
    const tl = new THREE.Group();
    const metalMat = new THREE.MeshLambertMaterial({ color: 0x334155 });
    const post = new THREE.Mesh(new THREE.CylinderGeometry(0.08, 0.08, 4.2, 8), metalMat);
    post.position.y = 2.1;
    post.castShadow = true;
    tl.add(post);

    // Housing box
    const box = new THREE.Mesh(new THREE.BoxGeometry(0.65, 1.6, 0.4), new THREE.MeshLambertMaterial({ color: 0x1E293B }));
    box.position.set(0, 3.4, 0.25);
    box.castShadow = true;
    tl.add(box);

    // 3 Lamps
    const redMat = new THREE.MeshBasicMaterial({ color: initialState === 'red' ? 0xEF4444 : 0x4B1818 });
    const yellowMat = new THREE.MeshBasicMaterial({ color: initialState === 'yellow' ? 0xF59E0B : 0x4D3608 });
    const greenMat = new THREE.MeshBasicMaterial({ color: initialState === 'green' ? 0x10B981 : 0x063B26 });

    const lampGeo = new THREE.CylinderGeometry(0.21, 0.21, 0.06, 20);
    lampGeo.rotateX(Math.PI / 2);

    const redLamp = new THREE.Mesh(lampGeo, redMat);
    redLamp.position.set(0, 3.85, 0.46);
    tl.add(redLamp);

    const yellowLamp = new THREE.Mesh(lampGeo, yellowMat);
    yellowLamp.position.set(0, 3.4, 0.46);
    tl.add(yellowLamp);

    const greenLamp = new THREE.Mesh(lampGeo, greenMat);
    greenLamp.position.set(0, 2.95, 0.46);
    tl.add(greenLamp);
    const lamps = [redLamp, yellowLamp, greenLamp];
    const activeColors = [0xFF3838, 0xFFD52A, 0x36FF88];
    const glows = lamps.map((lamp, i) => {
      const glow = window.PDD_VEHICLES.addGlow(lamp, activeColors[i], 1.2);
      glow.position.z = 0.08;
      return glow;
    });
    function showSignal(s) {
      lamps.forEach((lamp, i) => {
        const active = ['red', 'yellow', 'green'][i] === s || (s === 'flashing_yellow' && i === 1);
        lamp.material.color.setHex(active ? activeColors[i] : [0x351719, 0x352D14, 0x123126][i]);
        glows[i].visible = active;
      });
    }
    showSignal(initialState);
    if (arrow) {
      const canvas = document.createElement('canvas');
      canvas.width = canvas.height = 128;
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#172020'; ctx.fillRect(0, 0, 128, 128);
      ctx.strokeStyle = '#35F088'; ctx.lineWidth = 12;
      ctx.lineCap = 'round'; ctx.lineJoin = 'round';
      ctx.beginPath();
      if (arrow === 'right') {
        ctx.moveTo(24, 64); ctx.lineTo(102, 64); ctx.moveTo(70, 32); ctx.lineTo(102, 64); ctx.lineTo(70, 96);
      } else {
        ctx.moveTo(64, 104); ctx.lineTo(64, 24); ctx.moveTo(32, 56); ctx.lineTo(64, 24); ctx.lineTo(96, 56);
      }
      ctx.stroke();
      const face = new THREE.Mesh(new THREE.PlaneGeometry(0.64, 0.64),
        new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(canvas) }));
      face.position.set(0.7, 2.95, 0.47);
      face.userData.arrowSection = true;
      tl.add(face);
      window.PDD_VEHICLES.addGlow(face, 0x36FF88, 0.85).material.opacity = 0.4;
      tl.userData.arrow = arrow;
    }
    if (initialState === 'flashing_yellow') {
      yellowMat.color.setHex(0xF59E0B);
      tl.userData.beacons = [yellowLamp];
    }

    tl.setLightState = function(s) {
      lamps.forEach(lamp => { lamp.visible = true; });
      tl.userData.beacons = s === 'flashing_yellow' ? [yellowLamp] : [];
      showSignal(s);
    };
    tl.scale.setScalar(1.16);
    return tl;
  }

  // --- Low-Poly Environment Props (Trees, Buildings) ---
  // One material per mesh, never shared: retired segments receive clipping
  // planes and faded buildings change opacity on their materials, so a shared
  // material would clip or fade every tree/house of that colour in the world.
  const sceneryMat = color => new THREE.MeshLambertMaterial({ color });
  // Bake many small static meshes (windows, dashes, zebra stripes, posts) into
  // ONE mesh: draw calls, not triangles, are what weak phone GPUs choke on.
  function mergeStatic(meshes, material) {
    const positions = [], normals = [], uvs = [], sides = [];
    const normalMatrix = new THREE.Matrix3();
    // Texture coordinates and face flags baked by road-materials.js survive
    // merging; parts without them get zeros so the arrays stay aligned.
    const withUv = meshes.some(m => m.geometry.attributes.uv), withSide = meshes.some(m => m.geometry.attributes.pddSide);
    meshes.forEach(mesh => {
      if (mesh.matrixAutoUpdate) mesh.updateMatrix();
      const geometry = mesh.geometry.index ? mesh.geometry.toNonIndexed() : mesh.geometry;
      const p = geometry.attributes.position, n = geometry.attributes.normal, uv = geometry.attributes.uv, side = geometry.attributes.pddSide;
      normalMatrix.getNormalMatrix(mesh.matrix);
      const v = new THREE.Vector3();
      for (let i = 0; i < p.count; i++) {
        v.fromBufferAttribute(p, i).applyMatrix4(mesh.matrix); positions.push(v.x, v.y, v.z);
        v.fromBufferAttribute(n, i).applyMatrix3(normalMatrix).normalize(); normals.push(v.x, v.y, v.z);
        if (withUv) uvs.push(uv ? uv.getX(i) : 0, uv ? uv.getY(i) : 0);
        if (withSide) sides.push(side ? side.getX(i) : 0);
      }
      if (geometry !== mesh.geometry) geometry.dispose();
    });
    const merged = new THREE.BufferGeometry();
    merged.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
    merged.setAttribute('normal', new THREE.Float32BufferAttribute(normals, 3));
    if (uvs.length) merged.setAttribute('uv', new THREE.Float32BufferAttribute(uvs, 2));
    if (sides.length) merged.setAttribute('pddSide', new THREE.Float32BufferAttribute(sides, 1));
    const mesh = new THREE.Mesh(merged, material);
    if (material?.userData?.pddKind) mesh.userData.pddSkinned = material.userData.pddKind;
    return mesh;
  }
  // Bake several scenery groups (trees, houses) into one mesh per colour:
  // the far background costs a handful of draw calls per row, not dozens.
  function bakeGroups(groups) {
    const buckets = new Map();
    groups.forEach(group => {
      group.updateMatrixWorld(true);
      group.traverse(child => {
        if (!child.isMesh || !child.material?.color) return;
        // One bucket per colour, material type and surface kind (a tile roof
        // never shares a merged mesh with a plain part of the same colour).
        const key = child.material.color.getHex() + (child.material.isMeshBasicMaterial ? 'b' : 'l') + (child.material.userData.pddKind || '');
        if (!buckets.has(key)) buckets.set(key, { material: child.material, meshes: [] });
        const proxy = new THREE.Mesh(child.geometry, null);
        proxy.matrix.copy(child.matrixWorld); proxy.matrixAutoUpdate = false;
        buckets.get(key).meshes.push(proxy);
      });
    });
    return [...buckets.values()].map(b => { const m = mergeStatic(b.meshes, b.material); m.castShadow = false; m.userData.baked = true; return m; });
  }
  function createTree(kind) {
    const tree = new THREE.Group();
    kind = kind || ['pine', 'pine', 'round', 'round', 'birch'][Math.floor(Math.random() * 5)];
    const sn = season(), pick = list => list[Math.floor(Math.random() * list.length)];
    if (kind === 'birch') {
      const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.18, 3.2, 6), sceneryMat(0xE8E4DA));
      trunk.position.y = 1.6; trunk.castShadow = true; tree.add(trunk);
      const canopy = new THREE.Mesh(new THREE.SphereGeometry(1.1, 7, 6), sceneryMat(Math.random() < 0.7 ? sn.birch : pick(sn.canopy)));
      canopy.material.userData.seasonal = 'birch';
      canopy.scale.set(0.8, 1.35, 0.8); canopy.position.y = 3.6; canopy.castShadow = true; tree.add(canopy);
    } else if (kind === 'round') {
      const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.2, 0.3, 1.6, 6), sceneryMat(0x5D4037));
      trunk.position.y = 0.8; trunk.castShadow = true; tree.add(trunk);
      const canopy = new THREE.Mesh(new THREE.SphereGeometry(1.5, 8, 6), sceneryMat(pick(sn.canopy)));
      canopy.material.userData.seasonal = 'canopy';
      canopy.position.y = 2.6; canopy.castShadow = true; tree.add(canopy);
    } else {
      const trunk = new THREE.Mesh(new THREE.CylinderGeometry(0.2, 0.28, 1.5, 6), sceneryMat(0x5D4037));
      trunk.position.y = 0.75; trunk.castShadow = true; tree.add(trunk);
      const foliageColor = pick(sn.pine);
      const lower = new THREE.Mesh(new THREE.ConeGeometry(1.4, 2.4, 7), sceneryMat(foliageColor));
      lower.position.y = 2.2; lower.castShadow = true; tree.add(lower);
      const upper = new THREE.Mesh(new THREE.ConeGeometry(0.95, 1.9, 7), sceneryMat(foliageColor));
      upper.position.y = 3.5; upper.castShadow = true; tree.add(upper);
    }
    const scale = 0.8 + Math.random() * 0.5;
    tree.scale.set(scale, scale, scale);
    tree.rotation.y = Math.random() * Math.PI * 2;
    return tree;
  }
  function createBush(color) {
    const sn = season();
    color = color || (sn.precipitation === 'snow' ? 0xC9D2D8 : sn.roof === null && sn.sun === 0xFFE3B8 ? 0x9A8A3E : 0x56764C);
    const bush = new THREE.Mesh(new THREE.SphereGeometry(0.6, 7, 5), sceneryMat(color));
    bush.scale.set(0.7 + Math.random() * 0.5, 0.6, 1 + Math.random() * 0.6);
    bush.position.y = 0.55;
    return bush;
  }
  // A small dog on a leash, attached to a walker (local coords: +Z is the
  // walker's forward). Legs swing with the walker's gait.
  function createDog(color = 0x8A6A4A) {
    const dog = new THREE.Group();
    const fur = sceneryMat(color), dark = sceneryMat(0x2B2F33);
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.22, 0.22, 0.5), fur); body.position.set(0, 0.36, 0); dog.add(body);
    const head = new THREE.Mesh(new THREE.BoxGeometry(0.2, 0.2, 0.22), fur); head.position.set(0, 0.5, 0.32); dog.add(head);
    const nose = new THREE.Mesh(new THREE.BoxGeometry(0.08, 0.08, 0.06), dark); nose.position.set(0, 0.46, 0.45); dog.add(nose);
    [-1, 1].forEach(sx => { const ear = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.12, 0.08), fur); ear.position.set(sx * 0.09, 0.6, 0.28); dog.add(ear); });
    const tail = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.05, 0.22), fur); tail.position.set(0, 0.45, -0.32); tail.rotation.x = -0.6; dog.add(tail);
    dog.userData.legs = [];
    [[-0.07, 0.17], [0.07, 0.17], [-0.07, -0.17], [0.07, -0.17]].forEach(([x, z]) => {
      const hip = new THREE.Group(); hip.position.set(x, 0.27, z);
      const leg = new THREE.Mesh(new THREE.BoxGeometry(0.06, 0.27, 0.06), fur); leg.position.y = -0.13; hip.add(leg);
      dog.add(hip); dog.userData.legs.push(hip);
    });
    dog.traverse(o => { if (o.isMesh) o.castShadow = true; });
    return dog;
  }
  // A cat that potters about on a front lawn.
  function createCat(color = 0x5B5B5B) {
    const cat = new THREE.Group();
    const fur = sceneryMat(color);
    const body = new THREE.Mesh(new THREE.BoxGeometry(0.16, 0.16, 0.42), fur); body.position.set(0, 0.2, 0); cat.add(body);
    const head = new THREE.Mesh(new THREE.BoxGeometry(0.16, 0.15, 0.15), fur); head.position.set(0, 0.3, 0.26); cat.add(head);
    [-1, 1].forEach(sx => { const ear = new THREE.Mesh(new THREE.ConeGeometry(0.035, 0.08, 4), fur); ear.position.set(sx * 0.055, 0.4, 0.24); cat.add(ear); });
    const tail = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.04, 0.3), fur); tail.position.set(0, 0.32, -0.3); tail.rotation.x = -1.1; cat.add(tail);
    cat.userData.legs = []; cat.userData.tail = tail;
    [[-0.05, 0.14], [0.05, 0.14], [-0.05, -0.14], [0.05, -0.14]].forEach(([x, z]) => {
      const hip = new THREE.Group(); hip.position.set(x, 0.14, z);
      const leg = new THREE.Mesh(new THREE.BoxGeometry(0.04, 0.14, 0.04), fur); leg.position.y = -0.07; hip.add(leg);
      cat.add(hip); cat.userData.legs.push(hip);
    });
    return cat;
  }
  function createLampPost() {
    const lamp = new THREE.Group();
    const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.07, 0.1, 5.2, 6), null);
    pole.position.y = 2.6;
    const arm = new THREE.Mesh(new THREE.BoxGeometry(1.4, 0.08, 0.08), null);
    arm.position.set(-0.6, 5.1, 0);
    lamp.add(mergeStatic([pole, arm], sceneryMat(0x5B646A))); pole.geometry.dispose(); arm.geometry.dispose();
    const head = new THREE.Mesh(new THREE.BoxGeometry(0.5, 0.16, 0.26), new THREE.MeshBasicMaterial({ color: 0xE6E9D8 }));
    head.position.set(-1.25, 5.05, 0); lamp.add(head);
    return lamp;
  }
  // A picket fence: posts every 1.2 m, two rails and pointed pickets, all
  // one mesh in a wood material. Same 1 m height and footprint as before.
  function createFence(length) {
    const fence = new THREE.Group(), parts = [];
    const add = (geo, x, y, z) => { const m = new THREE.Mesh(geo); m.position.set(x, y, z); parts.push(m); };
    const postGeo = new THREE.BoxGeometry(0.1, 1, 0.1), railGeo = new THREE.BoxGeometry(0.05, 0.07, length);
    const board = new THREE.BoxGeometry(0.025, 0.82, 0.085), tip = new THREE.CylinderGeometry(0, 0.06, 0.1, 4);
    for (let z = -length / 2; z <= length / 2 + 1e-6; z += 1.2) add(postGeo, 0, 0.5, z);
    add(railGeo, 0.06, 0.3, 0); add(railGeo, 0.06, 0.72, 0);
    for (let z = -length / 2 + 0.11; z < length / 2 - 0.05; z += 0.17) { add(board, 0.1, 0.41, z); add(tip, 0.1, 0.87, z); }
    const mesh = mergeStatic(parts, sceneryMat(0x8A7660));
    window.PDD_ROADS.skinObject(mesh, 'wood'); fence.add(mesh);
    [postGeo, railGeo, board, tip].forEach(g => g.dispose());
    return fence;
  }
  function createParkedCar() {
    const colors = [0xE8E8E8, 0x2F3A46, 0x8B1E2D, 0x6E86A6, 0xC9B36B, 0x4D756A, 0xB87847, 0xD1CEC4];
    const car = createNpcCar(colors[Math.floor(Math.random() * colors.length)]);
    car.traverse(o => { o.userData.scenery = true; });
    return car;
  }
  function createKiosk() {
    const kiosk = new THREE.Group();
    const palette = [[0x4F7C8A, 0xE0533F], [0x879077, 0xE1BF74], [0xB78972, 0x3D6A81]][Math.floor(Math.random() * 3)];
    const body = new THREE.Mesh(new THREE.BoxGeometry(2.4, 2.4, 2), sceneryMat(palette[0]));
    body.position.y = 1.2; kiosk.add(body); window.PDD_ROADS.skinObject(body, 'metal');
    const glass = new THREE.Mesh(new THREE.PlaneGeometry(1.8, 1), new THREE.MeshBasicMaterial({ color: 0x9FC2CE }));
    glass.position.set(0, 1.4, 1.01); kiosk.add(glass); window.PDD_ROADS.skinObject(glass, 'window');
    const awning = new THREE.Mesh(new THREE.BoxGeometry(2.8, 0.08, 0.9), sceneryMat(palette[1]));
    awning.position.set(0, 2.15, 1.35); awning.rotation.x = 0.25; kiosk.add(awning);
    return kiosk;
  }
  function createPond() {
    const pond = new THREE.Group();
    const water = new THREE.Mesh(new THREE.CircleGeometry(4.2, 18), sceneryMat(season().precipitation === 'snow' ? 0xD7E6EE : 0x6FA8C9));
    water.material.userData.seasonal = 'water';
    water.rotation.x = -Math.PI / 2; water.scale.set(1.4, 1, 1); water.position.y = 0.012; pond.add(water);
    const shore = new THREE.Mesh(new THREE.CircleGeometry(4.7, 18), sceneryMat(0xC9BFA6));
    shore.rotation.x = -Math.PI / 2; shore.scale.set(1.4, 1, 1); shore.position.y = 0.006; pond.add(shore);
    for (let i = 0; i < 3; i++) {
      const reed = new THREE.Mesh(new THREE.CylinderGeometry(0.05, 0.08, 1.1, 5), sceneryMat(0x6C8C3F));
      const a = i * 2.1 + 0.4; reed.position.set(Math.cos(a) * 5.4, 0.55, Math.sin(a) * 3.9); pond.add(reed);
    }
    return pond;
  }
  // Facade skins (road-materials.js): panel seams sit 0.4 m before the first
  // window column (windows start 1.4 m in, every 2 m) and between storeys
  // (windows at 1.8 m + 2.7 m steps).
  const WALL = {
    plaster: mesh => window.PDD_ROADS.skinObject(mesh, 'plaster', { v0: -0.2 }),
    panel: mesh => window.PDD_ROADS.skinObject(mesh, 'panel', { u0: -0.4, v0: -0.45 }),
    brick: mesh => window.PDD_ROADS.skinObject(mesh, 'brick'),
  };
  function createBuilding(width = 12, height = 14, depth = 12, style = 2) {
    const b = new THREE.Group();
    b.userData.cameraOccluder = true;
    const palettes = { 1: [0xF3E3C3, 0xE8CFA8, 0xD9B99B, 0xC8D9C0, 0xE9D5CC], 2: [...BRAND.buildingColors, 0xB5675A, 0xA9B4C2] };
    const palette = palettes[style] || BRAND.buildingColors;
    const color = palette[Math.floor(Math.random() * palette.length)];
    // Own materials only: the camera-occlusion fade mutates them per building.
    const body = new THREE.Mesh(new THREE.BoxGeometry(width, height, depth), sceneryMat(color));
    // Facade: plaster on houses; on blocks large panels whose seams fall
    // between the window rows and columns, or brick for the red-brown ones.
    // (Chosen from the size, not Math.random: the random sequence stays as before.)
    const brick = style === 2 && (color === 0xB5675A || (color === 0xDDE1EA && Math.floor(width * 3 + depth) % 3 === 0));
    if (style === 1) WALL.plaster(body);
    else if (brick) WALL.brick(body);
    else WALL.panel(body);
    body.position.y = height / 2;
    body.castShadow = false; // Avoid square shadows cast by buildings outside the viewport.
    body.receiveShadow = true;
    b.add(body);

    if (style === 1) {
      // Low houses: hip roof in tile or slate.
      // Unit square pyramid (rotated in the geometry so scaling stays axis-aligned),
      // stretched to the footprint plus a small eave.
      const roofGeo = new THREE.ConeGeometry(Math.SQRT2 / 2, 1, 4); roofGeo.rotateY(Math.PI / 4);
      const roof = new THREE.Mesh(roofGeo, sceneryMat(season().roof || (Math.random() > 0.5 ? 0x8C4A3C : 0x5D6B75)));
      roof.material.userData.seasonal = 'roof';
      // Eaves: a dark strip under the roof edge keeps the silhouette readable
      // against snow (and reads as a shadow line in any season).
      const eave = new THREE.Mesh(new THREE.BoxGeometry(width + 0.9, 0.18, depth + 0.9), sceneryMat(0x4A4F55));
      eave.position.y = height + 0.02; b.add(eave);
      roof.scale.set(width + 0.8, 2.4, depth + 0.8);
      roof.position.y = height + 1.2; b.add(roof);
      // Tile rows of about 0.3 m along the slopes, at the roof's true size.
      const slant = Math.hypot(2.4, Math.min(width, depth) / 2 + 0.4);
      window.PDD_ROADS.skinObject(roof, 'roofTile', { su: 2 * (width + depth + 1.6) / 1.2, sv: slant / 1.2 });
    } else {
      // Flat roof slab (tar; snow-grey in winter) so the top never shows the facade colour.
      const slab = new THREE.Mesh(new THREE.BoxGeometry(width - 0.2, 0.08, depth - 0.2), sceneryMat(season().precipitation === 'snow' ? 0xB9C2CA : 0x6B7480));
      slab.position.y = height + 0.04; b.add(slab); window.PDD_ROADS.skinObject(slab, 'roofFlat');
      const roofBorder = new THREE.Mesh(new THREE.BoxGeometry(width + 0.4, 0.4, depth + 0.4), sceneryMat(season().precipitation === 'snow' ? 0x7F8B99 : 0x94A3B8));
      roofBorder.position.y = height + 0.2; b.add(roofBorder); window.PDD_ROADS.skinObject(roofBorder, 'roofFlat');
      if (Math.random() > 0.5) {
        const box = new THREE.Mesh(new THREE.BoxGeometry(2.2, 1.4, 2), sceneryMat(0x8391A0));
        box.position.set(width * 0.2, height + 0.7, -depth * 0.2); b.add(box);
      }
    }

    const glass = new THREE.MeshBasicMaterial({ color: [0x708995, 0x647D87, 0x87988F][Math.floor(Math.random() * 3)] });
    const windowGeo = new THREE.PlaneGeometry(Math.random() < 0.5 ? 1 : 1.3, 1.25);
    const windows = [];
    for (const side of [-1, 1]) {
      for (let y = 1.8; y < height - 0.6; y += 2.7) {
        for (let z = -depth / 2 + 1.4; z < depth / 2 - 0.6; z += 2) {
          const window = new THREE.Mesh(windowGeo, glass);
          window.position.set(side * (width / 2 + 0.015), y, z);
          window.rotation.y = side * Math.PI / 2;
          windows.push(window);
        }
        for (let x = -width / 2 + 1.3; x < width / 2 - 0.6; x += 2) {
          const window = new THREE.Mesh(windowGeo, glass);
          window.position.set(x, y, side * (depth / 2 + 0.015));
          window.rotation.y = side > 0 ? 0 : Math.PI;
          windows.push(window);
        }
      }
      const door = new THREE.Mesh(new THREE.PlaneGeometry(0.95, 1.9), sceneryMat(0x536666));
      door.position.set(side * (width / 2 + 0.02), 0.95, 0);
      door.rotation.y = side * Math.PI / 2; b.add(door); window.PDD_ROADS.skinObject(door, 'door');
      if (side === 1) {
        // Frames, sills and a reflection come from the shared window map.
        const merged = mergeStatic(windows, glass); window.PDD_ROADS.skinObject(merged, 'window');
        b.add(merged); b.userData.windows = merged; windowGeo.dispose();
      }
      if (style === 2 && Math.random() > 0.4) {
        // Ground-floor shop awning on the street side.
        const awning = new THREE.Mesh(new THREE.BoxGeometry(0.9, 0.08, Math.min(depth - 1, 4)),
          sceneryMat([0xE0533F, 0x2F6F9F, 0x3E8E5E, 0xD9A441][Math.floor(Math.random() * 4)]));
        awning.position.set(side * (width / 2 + 0.45), 2.45, 0); awning.rotation.z = -side * 0.28; b.add(awning);
      }
    }
    return b;
  }

  // Adjacent surfaces overlap by this much: quads that merely touch leave a
  // sub-pixel antialiased seam through which the ground shows as a 1px line.
  // Overlaps are same-colour, so the coplanar overlap itself is invisible.
  const SEAM = 0.12;
  // Centre of each island of the three-carriageway road (ticket 28.2).
  const THREE_ISLAND_Z = 5.23;

  // oneWay: null (two-way), 'with' (the player drives with the one-way flow)
  // or 'against' (the player entered it against the flow, a violation).
  // backdropFrom: no far background (x 30-70) in the first metres of the
  // road. A cross street starting at a junction leaves its corners to the
  // main street's background: both used to put houses on the same plots.
  function buildStraightSegment(startZ, length = 70, preview = false, district = state.district, oneWay = null, backdropFrom = 0) {
    const seg = new THREE.Group();
    const roadWidth = 8.4; // 2 lanes (4.2m each)

    // Asphalt
    const asphalt = new THREE.Mesh(
      new THREE.PlaneGeometry(roadWidth, length + 2 * SEAM),
      new THREE.MeshLambertMaterial({ color: BRAND.asphalt })
    );
    asphalt.rotation.x = -Math.PI / 2;
    asphalt.position.set(0, 0.02, startZ + length / 2);
    asphalt.receiveShadow = true;
    seg.add(asphalt);

    // Sidewalks: exactly 4.2 ... 7.4 across, like every pavement piece. A SEAM
    // overlap across (into the road) left a 12 cm step where the pavement
    // meets a rounded corner; only pieces laid end to end need to overlap.
    const swWidth = 3.2;
    const swL = new THREE.Mesh(
      new THREE.BoxGeometry(swWidth, 0.18, length + 2 * SEAM),
      new THREE.MeshLambertMaterial({ color: BRAND.sidewalk })
    );
    swL.position.set(-(roadWidth / 2 + swWidth / 2), 0.09, startZ + length / 2);
    swL.receiveShadow = true;
    seg.add(swL);

    const swR = new THREE.Mesh(
      new THREE.BoxGeometry(swWidth, 0.18, length + 2 * SEAM),
      new THREE.MeshLambertMaterial({ color: BRAND.sidewalk })
    );
    swR.position.set(roadWidth / 2 + swWidth / 2, 0.09, startZ + length / 2);
    swR.receiveShadow = true;
    seg.add(swR);

    // Center Dashed Marking (1.5)
    const dashLength = 2.0;
    const gapLength = 3.0;
    const markingMat = new THREE.MeshBasicMaterial({ color: BRAND.asphaltMarking });
    const dashGeo = new THREE.PlaneGeometry(0.18, dashLength);
    dashGeo.rotateX(-Math.PI / 2);

    const dashes = [];
    for (let z = startZ + 2; z < startZ + length - 2; z += (dashLength + gapLength)) {
      const dash = new THREE.Mesh(dashGeo, markingMat);
      dash.position.set(0, 0.025, z + dashLength / 2);
      dashes.push(dash);
    }
    seg.add(mergeStatic(dashes, markingMat));

    // Outer Solid Lines (1.2)
    const solidLineGeo = new THREE.PlaneGeometry(0.15, length);
    solidLineGeo.rotateX(-Math.PI / 2);
    const lineL = new THREE.Mesh(solidLineGeo, markingMat);
    lineL.position.set(-roadWidth / 2 + 0.25, 0.025, startZ + length / 2);
    seg.add(lineL);

    const lineR = new THREE.Mesh(solidLineGeo, markingMat);
    lineR.position.set(roadWidth / 2 - 0.25, 0.025, startZ + length / 2);
    seg.add(lineR);

    if (oneWay) {
      // Both lanes carry the same direction: the centre dashes are the lane
      // divider 1.5. 5.5 starts the one-way stretch, 5.6 ends it before the
      // next (two-way) junction. Against the flow the driver sees their backs.
      const flowForward = oneWay === 'with';
      const place = (code, z) => {
        const sign = createRoadSign(code);
        // On the flow's right-hand pavement (factory X = driver's right).
        sign.position.set(flowForward ? 5.2 : -5.2, 0, z);
        sign.rotation.y = flowForward ? 0 : Math.PI;
        seg.add(sign);
      };
      place('5.5', flowForward ? startZ + 6 : startZ + length - 6);
      place('5.6', flowForward ? startZ + length - 14 : startZ + 14);
    }

    // Districts blend over the road's length, and are built with the road,
    // never spawned in response to a camera turn: park / homes / boulevard.
    seg.userData.district = district;
    for (let z = startZ + 8, row = 0; z < startZ + length - 8; z += 20, row++) {
      const t = THREE.MathUtils.smoothstep((z - startZ) / length, 0.2, 0.8);
      const next = (district + 1) % DISTRICTS;
      const style = row % 5 / 4 < t ? next : district;
      for (const side of [-1, 1]) {
        const vergeGeometry = new THREE.PlaneGeometry(22 + SEAM, 20 + SEAM);
        const verge = new THREE.Mesh(vergeGeometry, new THREE.MeshLambertMaterial({ color: season().verge[Math.min(style, 2)] }));
        verge.material.userData.seasonal = 'verge' + Math.min(style, 2);
        verge.rotation.x = -Math.PI / 2; verge.position.set(side * 18.4, -0.015, z);
        verge.receiveShadow = true; seg.add(verge);
        // The far background beyond the verge (x 30-70): forest, distant
        // houses or tall blocks, fields and a hill, so a glance sideways never
        // ends in empty grass. Baked per row into a few meshes.
        const far = [];
        if (z - startZ < backdropFrom) {
          // Left to the main street's background at a junction corner.
        } else if (style === 0 || row % 3 === 2) {
          for (let i = 0; i < 7; i++) {
            const tree = createTree(i % 3 === 0 ? 'pine' : undefined);
            tree.position.set(side * (28 + Math.random() * 18), 0, z - 9 + Math.random() * 18);
            tree.scale.multiplyScalar(1.1); far.push(tree);
          }
          if (row % 2 === 0) {
            const field = new THREE.Mesh(new THREE.PlaneGeometry(26, 18), new THREE.MeshLambertMaterial({ color: season().verge[1] }));
            field.rotation.x = -Math.PI / 2; field.position.set(side * 50, -0.012, z); far.push(field);
          }
        } else if (style === 1) {
          // Side by side by their widths, with a gap (random fixed steps let
          // two wide ones grow into each other).
          for (let i = 0, x = 29 + Math.random() * 2; i < 2; i++) {
            const w = 6 + Math.random() * 2, d = 6 + Math.random() * 2;
            const house = createBuilding(w, 4.5, d, 1);
            house.position.set(side * (x + w / 2), 0, z - 4 + Math.random() * 8);
            house.rotation.y = Math.random() * 0.6 - 0.3; far.push(house);
            x += w + 2.5 + Math.random() * 2; // room for the ±0.3 rad turn
          }
          for (let i = 0; i < 3; i++) { const tree = createTree('round'); tree.position.set(side * (32 + Math.random() * 16), 0, z - 8 + Math.random() * 16); far.push(tree); }
        } else if (style === 3) {
          for (let i = 0, x = 29 + Math.random() * 3; i < 2; i++) {
            const w = 14 + Math.random() * 4;
            const tower = createBuilding(w, 30 + Math.random() * 18, 12, 2);
            tower.position.set(side * (x + w / 2), 0, z - 5 + Math.random() * 10); far.push(tower);
            x += w + 1.5 + Math.random() * 2;
          }
        } else {
          for (let i = 0, x = 26 + Math.random() * 3; i < 2; i++) {
            const w = 10 + Math.random() * 4;
            const block = createBuilding(w, 12 + Math.random() * 12, 9 + Math.random() * 3, 2);
            block.position.set(side * (x + w / 2), 0, z - 6 + Math.random() * 12); far.push(block);
            x += w + 1.5 + Math.random() * 2;
          }
        }
        if (row === 0 && Math.random() < 0.5) {
          const hill = new THREE.Mesh(new THREE.SphereGeometry(22, 12, 8), new THREE.MeshLambertMaterial({ color: season().hillColor }));
          hill.scale.set(1.6, 0.32, 1); hill.position.set(side * 66, -2, z + 20); far.push(hill);
        }
        const backdrop = new THREE.Group();
        bakeGroups(far).forEach(m => backdrop.add(m));
        seg.add(backdrop);
        // Rows are 20 m apart; a building of depth D leaves a gap of 20 - D
        // where trees, hedges and parked cars go (never under a facade).
        const depth = style === 0 ? 0 : style === 1 ? 6 + Math.random() * 2 : style === 3 ? 11 : 8 + Math.random() * 2;
        const gapZ = z + depth / 2 + (20 - depth) / 2;
        // The chase camera looks down +Z: scenery must sit in FRONT of a facade
        // (smaller z) to stay visible, never right behind one.
        // A facade of height H hides ~H metres of ground behind it at this camera
        // pitch, so trees stand just in front of the NEXT facade; on the boulevard
        // (tall facades) they are street trees on the outer half of the pavement.
        const tree = createTree(); tree.position.set(side * 8.6, 0, style === 0 ? z - 3 : gapZ + 3.5);
        tree.scale.setScalar(style >= 2 ? 0.8 : 1); seg.add(tree);
        if (style !== 0) {
          // High-rise blocks: 9–16 storey towers set back behind a lawn strip.
          const floors = style === 1 ? (Math.random() < 0.7 ? 1 : 2) : style === 3 ? 9 + Math.floor(Math.random() * 8) : 3 + Math.floor(Math.random() * 3);
          const width = style === 1 ? 6 + Math.random() * 2 : style === 3 ? 13 + Math.random() * 3 : 10 + Math.random() * 3;
          const building = createBuilding(width, floors * 3 + 1.5, depth, style === 3 ? 2 : style);
          // Homes stand 0.8 m behind their yard fence (8.0) whatever their
          // width: a wide one used to put its facade right on the fence line.
          building.position.set(side * (style === 1 ? 8.8 + width / 2 : style === 3 ? 18.5 : 13.5), 0, z); seg.add(building);
          state.occluders.push(building);
        }
        // Street furniture and district flavour, all outside the carriageway.
        if (row % 2 === (side > 0 ? 1 : 0)) {
          const lamp = createLampPost(); lamp.position.set(side * 7.0, 0, z - 9); lamp.rotation.y = side > 0 ? Math.PI : 0; seg.add(lamp);
        }
        if (style === 0) {
          // Park: second tree line, bushes, an occasional pond.
          const back = createTree(); back.position.set(side * (14 + Math.random() * 6), 0, z + 4 + Math.random() * 6); seg.add(back);
          const shrub = createBush(); shrub.position.x = side * (10.5 + Math.random() * 2); shrub.position.z = z - 1; seg.add(shrub);
          if (row % 3 === 1) { const pond = createPond(); pond.position.set(side * 20, 0, z + 2); seg.add(pond); }
        } else if (style === 1) {
          // Homes: fenced yards with a parked car or a hedge.
          const fence = createFence(depth + 6); fence.position.set(side * 8.0, 0, z + 1); seg.add(fence);
          if (Math.random() < 0.22) {
            const cat = createCat([0x5B5B5B, 0xD8863B, 0xEDE6DA, 0x2A2A2A][Math.floor(Math.random() * 4)]);
            cat.position.set(side * 9.4, 0, gapZ + 1); seg.add(cat);
            state.ambient.push({ mesh: cat, center: gapZ + 1, phase: Math.random() * 6, time: 0, kind: 'cat', seg, side, lane: 0, targetLane: 0 });
          }
          if (row % 2 === 0) {
            const parked = createParkedCar(); parked.position.set(side * 12.8, 0, gapZ - 0.5); parked.rotation.y = side * Math.PI / 2 + 0.15; seg.add(parked);
          } else {
            const hedge = createBush(); hedge.scale.set(1.2, 0.9, 3); hedge.position.set(side * 12.8, 0.5, gapZ - 0.5); seg.add(hedge);
          }
        } else if (style === 3) {
          // Courtyards between towers: a parked car and a hedge.
          if (row % 2 === 0) { const parked = createParkedCar(); parked.position.set(side * 10.4, 0, gapZ - 0.5); parked.rotation.y = side * Math.PI / 2; seg.add(parked); }
          else { const hedge = createBush(); hedge.scale.set(1, 0.8, 2.6); hedge.position.set(side * 10.4, 0.4, gapZ - 0.5); seg.add(hedge); }
        } else {
          // Boulevard: kiosk or billboard between the tall facades.
          if (row % 3 === 0) { const kiosk = createKiosk(); kiosk.position.set(side * 9.4, 0, gapZ - 3.2); kiosk.rotation.y = side > 0 ? -Math.PI / 2 : Math.PI / 2; seg.add(kiosk); }
          else if (row % 3 === 2) {
            const board = new THREE.Mesh(new THREE.BoxGeometry(0.1, 1.6, 3), sceneryMat([0xF2C14E, 0x5DA9E9, 0xE07A5F][row % 3]));
            board.position.set(side * 8.6, 2.2, gapZ - 3.2);
            const billboard = new THREE.Group(); billboard.add(board); seg.add(billboard);
            const leg = new THREE.Mesh(new THREE.CylinderGeometry(0.06, 0.06, 1.4, 6), sceneryMat(0x5B646A));
            leg.position.set(side * 8.6, 0.7, gapZ - 3.2); billboard.add(leg);
          }
        }
        // A bench and planter form a quiet park edge, outside the walking lane.
        const bench = new THREE.Group();
        const wood = new THREE.MeshLambertMaterial({ color: 0x987856 });
        const pieces = [];
        for (const [w, h, d, y, offset] of [[1.6, 0.12, 0.5, 0.55, 0], [1.6, 0.5, 0.12, 0.85, 0.2]]) {
          const piece = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), wood);
          piece.position.set(0, y, offset); pieces.push(piece);
        }
        const legs = [];
        for (const x of [-0.6, 0.6]) {
          const leg = new THREE.Mesh(new THREE.BoxGeometry(0.1, 0.5, 0.4), null);
          leg.position.set(x, 0.25, 0); legs.push(leg);
        }
        bench.add(mergeStatic(pieces, wood), mergeStatic(legs, sceneryMat(0x495452)));
        [...pieces, ...legs].forEach(m => m.geometry.dispose());
        bench.position.set(side * 8.1, 0, z + (style === 0 ? 4 : 6)); bench.rotation.y = side * Math.PI / 2; seg.add(bench);
        const planter = new THREE.Mesh(new THREE.BoxGeometry(0.8, 0.45, 1.8),
          new THREE.MeshLambertMaterial({ color: style === 2 ? 0x8D999E : 0xB79774 }));
        planter.position.set(side * 8.1, 0.22, z + (style === 0 ? 7 : 8.5)); seg.add(planter);
        const bush = new THREE.Mesh(new THREE.SphereGeometry(0.6, 7, 5),
          new THREE.MeshLambertMaterial({ color: 0x56764C }));
        bush.scale.set(0.7, 0.6, 1.2); bush.position.set(side * 8.1, 0.6, z + (style === 0 ? 7 : 8.5)); seg.add(bush);
        // Ambient walkers have no traffic IDs, answers, badges or collisions.
        if (row % 2 === (side > 0 ? 0 : 1)) {
          const walker = createPedestrian(PEOPLE_COLORS[Math.floor(Math.random() * PEOPLE_COLORS.length)]);
          if (Math.random() < 0.14) {
            // Now and then someone walks a dog: it trots beside, on a leash.
            const dog = createDog([0x8A6A4A, 0xD9C6A5, 0x3A3A3A, 0xB88A5A][Math.floor(Math.random() * 4)]);
            dog.position.set(0.55, -0.18, -0.85); walker.add(dog); walker.userData.dog = dog;
            const leash = new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(0.3, 0.9, 0), new THREE.Vector3(0.55, 0.3, -0.55)]),
              new THREE.LineBasicMaterial({ color: 0x2B2F33 }));
            walker.add(leash);
          }
          const lane = row % 4 < 2 ? 0 : 1; // pavement has two walking lanes
          walker.position.set(side * (5.2 + lane * 1.1), 0.18, z);
          seg.add(walker);
          state.ambient.push({ mesh: walker, center: z, phase: row * 1.7, time: 0, side, lane, targetLane: lane, seg });
        }
      }
    }

    // Treat each complete roadside object as one unit when clearing a junction.
    // Cutting its individual meshes leaves open facades and floating furniture.
    seg.children.forEach(o => {
      const box = new THREE.Box3().setFromObject(o);
      if (!box.isEmpty() && box.max.y > 0.3) o.userData.sceneryObject = true;
    });
    registerRoadSegment(seg);
    seg.userData.oneWay = oneWay;
    seg.userData.roadEnds = [new THREE.Vector3(0, 0, startZ), new THREE.Vector3(0, 0, startZ + length)];
    addPuddles(seg, startZ, length);
    state.weatherDirty = true;
    if (preview) return seg;
    state.roadSegments.push(seg);
    return length;
  }

  // --- Crossroad & Situation Segment Generator ---
  // An unpaved road has its own surface and shoulders, rather than a brown
  // rectangle over a kerbed street. Distance is measured from the junction
  // mouth so the texture, ruts and uneven edges continue across segment seams.
  function dirtHalfWidth(distance) {
    const mouth = 3.2 * (1 - THREE.MathUtils.smoothstep(distance, 0, 3.2));
    return 4.2 + mouth + 0.14 * Math.sin(distance * 0.41) + 0.09 * Math.sin(distance * 0.93);
  }

  function addDirtSurface(group, from, to, phase = 0, fadeFrom = Infinity, fadeTo = Infinity) {
    const canvas = document.createElement('canvas');
    canvas.width = 256; canvas.height = Math.max(128, Math.ceil((to - from) * 16));
    const ctx = canvas.getContext('2d'), pixels = ctx.createImageData(canvas.width, canvas.height);
    const visualHalfWidth = 8.6; // Includes the flared mouth and feathered shoulders.
    for (let row = 0; row < canvas.height; row++) {
      const d = phase + from + row / (canvas.height - 1) * (to - from);
      const edge = dirtHalfWidth(d), wobble = 0.08 * Math.sin(d * 0.31) + 0.1 * Math.sin(d * 0.073);
      const fade = Number.isFinite(fadeTo) ? 1 - THREE.MathUtils.smoothstep(d, fadeFrom, fadeTo) : 1;
      for (let col = 0; col < canvas.width; col++) {
        const x = (col / (canvas.width - 1) * 2 - 1) * visualHalfWidth;
        let hash = Math.imul(Math.floor(x * 24), 73856093) ^ Math.imul(Math.floor(d * 16), 19349663);
        hash = Math.imul(hash ^ (hash >>> 13), 1274126177) >>> 0;
        const grain = (hash & 255) / 255;
        const rutDistance = Math.min(Math.abs(x - wobble - 2.55), Math.abs(x - wobble - 1.05),
          Math.abs(x - wobble + 1.05), Math.abs(x - wobble + 2.55));
        const rut = 1 - THREE.MathUtils.smoothstep(rutDistance, 0.06, 0.4);
        let fine = Math.imul(Math.floor(x * 48), 83492791) ^ Math.imul(Math.floor(d * 32), 2654435761);
        fine = (Math.imul(fine ^ (fine >>> 15), 2246822519) >>> 0) / 4294967296;
        const drift = 5 * Math.sin(d * 0.37 + x * 0.9) + 4 * Math.sin(d * 0.13 - x * 0.45);
        const pebble = fine > 0.955 ? 26 : fine < 0.03 ? -18 : 0;
        const variation = (grain - 0.5) * 16 * (1 - rut * 0.5) + (fine - 0.5) * 8 - rut * 15 + drift + pebble * (1 - rut * 0.6) + (grain > 0.975 ? 18 : 0);
        const verge = THREE.MathUtils.smoothstep(Math.abs(x) - edge, -0.9, 0.3) * 0.22;
        const mouthFade = THREE.MathUtils.smoothstep(d + (grain-.5)*.65, -3.2, .1);
        const alpha = (1 - THREE.MathUtils.smoothstep(Math.abs(x) - edge + (grain - 0.5) * 0.2, 0, 1.1)) * fade * mouthFade;
        const i = (row * canvas.width + col) * 4;
        pixels.data[i] = 148 + variation - verge * 30; pixels.data[i + 1] = 120 + variation + verge * 14; pixels.data[i + 2] = 84 + variation - verge * 6;
        pixels.data[i + 3] = Math.round(255 * alpha);
      }
    }
    ctx.putImageData(pixels, 0, 0);
    const texture = new THREE.CanvasTexture(canvas);
    texture.flipY = false; texture.anisotropy = Math.min(4, renderer.capabilities.getMaxAnisotropy());
    const material = new THREE.MeshLambertMaterial({ map: texture, transparent: true, depthWrite: false, side: THREE.DoubleSide });
    const strip = (left, right, drivable) => {
      // Short boxes follow the flared mouth without making the grass drivable.
      for (let a = from; a < to - 1e-6;) {
        const b = !drivable || phase + a >= 4 ? to : Math.min(to, a + 2);
        const mesh = addRibbon(group, a, b, left, right, 0.028, material, 0.5);
        const pos = mesh.geometry.attributes.position, uv = [];
        for (let i = 0; i < pos.count; i++) uv.push(0.5 + pos.getX(i) / (2 * visualHalfWidth), (pos.getZ(i) - from) / (to - from));
        mesh.geometry.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2));
        mesh.userData.dirtSurface = true; mesh.receiveShadow = true;
        if (drivable) mesh.userData.surface = 'road';
        a = b;
      }
    };
    const half = z => dirtHalfWidth(phase + z);
    strip(z => -half(z), half, true);
    strip(z => -half(z) - 1.1, z => -half(z), false);
    strip(half, z => half(z) + 1.1, false);
  }

  function buildDirtExit(length, district, phase) {
    const seg = new THREE.Group();
    // The unpaved arm continues well beyond the junction. At its far end soil
    // thins out over 30 m of asphalt; pavements and paint start only after it.
    const fadeFrom = 45, pavedFrom = 75;
    const ground = new THREE.Mesh(new THREE.PlaneGeometry(44, pavedFrom + 2 * SEAM),
      new THREE.MeshLambertMaterial({ color: season().verge[Math.min(district, 2)] }));
    ground.material.userData.seasonal = 'verge' + Math.min(district, 2);
    ground.rotation.x = -Math.PI / 2; ground.position.set(0, -0.015, pavedFrom / 2); seg.add(ground);
    roadSurface(seg, 8.4, pavedFrom - fadeFrom, 0, (fadeFrom + pavedFrom) / 2);
    addDirtSurface(seg, -SEAM, pavedFrom + SEAM, phase, phase + fadeFrom, phase + pavedFrom);
    for (let z = 10; z < pavedFrom - 10; z += 18) for (const side of [-1, 1]) {
      const tree = createTree(z % 3 ? 'round' : 'pine');
      tree.position.set(side * (11 + 2 * Math.sin(z)), 0, z); tree.userData.sceneryObject = true; seg.add(tree);
      const bush = createBush(); bush.position.set(side * 7.5, 0, z + 5); bush.userData.sceneryObject = true; seg.add(bush);
    }
    const paved = buildStraightSegment(pavedFrom, length - pavedFrom, true, district);
    seg.add(paved); scene.add(seg);
    seg.userData.district = district;
    seg.userData.dirtPavedFrom = pavedFrom;
    seg.userData.roadEnds = [new THREE.Vector3(0, 0, 0), new THREE.Vector3(0, 0, length)];
    return seg;
  }

  // One model per actor config, with beacons, badge and measured collision half-sizes.
  function createActorMesh(cfg) {
    let actorMesh;
    let badgeHeight = 2.4;

    if (cfg.type === 'tram') {
      actorMesh = createTram(cfg.color);
      actorMesh.scale.set(0.75, 0.75, 0.75);
      badgeHeight = 3.6;
    } else if (cfg.type === 'bus') {
      actorMesh = createBus(cfg.color);
      actorMesh.scale.set(0.85, 0.85, 0.85);
      badgeHeight = 3.2;
    } else if (cfg.type === 'tractor') {
      // Tractors come in the usual farm colours, not only the scenario's.
      actorMesh = createTractor(cfg.paint ?? [0xF2B233, 0x2F6FD6, 0xD63A2F, 0x3E9B4F][Math.floor(Math.random() * 4)]);
      badgeHeight = 3.6;
    } else if (cfg.type === 'truck' || cfg.type === 'tanker') {
      actorMesh = cfg.type === 'tanker' ? createTanker(cfg.color) : createTruck(cfg.color);
      actorMesh.scale.set(0.85, 0.85, 0.85);
      badgeHeight = 3.4;
    } else if (cfg.type === 'special') {
      actorMesh = createSpecialCar(cfg.color);
      badgeHeight = 2.4;
    } else if (cfg.type === 'van') {
      actorMesh = createVan(cfg.color);
      badgeHeight = 3.0;
    } else if (cfg.type === 'cart') {
      actorMesh = createHorseCart();
      badgeHeight = 3.0;
    } else if (cfg.type === 'train') {
      actorMesh = createTrain(cfg.tailColor);
      badgeHeight = 4.8;
    } else if (cfg.type === 'motorcycle') {
      actorMesh = cfg.sidecar ? createMotorcycleSidecar(cfg.color) : createMotorcycle(cfg.color);
      badgeHeight = 2.7;
    } else if (cfg.type === 'cyclist') {
      actorMesh = createCyclist(cfg.color);
      badgeHeight = 2.7;
    } else if (cfg.type === 'pedestrian') {
      actorMesh = createPedestrian(cfg.color);
      badgeHeight = 2.8;
    } else {
      actorMesh = createNpcCar(cfg.color);
      badgeHeight = 2.4;
    }
    if (cfg.beacon === 'amber') {
      const beacon = new THREE.Mesh(new THREE.CylinderGeometry(0.16, 0.2, 0.2, 10),
        new THREE.MeshBasicMaterial({ color: 0xFFB21C }));
      beacon.position.set(0, badgeHeight - 0.4, 0);
      actorMesh.add(beacon);
      actorMesh.userData.beacons = [beacon];
      window.PDD_VEHICLES.addGlow(beacon, 0xFFB21C, 1.7);
    }
    if (cfg.beacon === 'blue' && actorMesh.userData.beacons) {
      actorMesh.userData.beacons.forEach(l => {
        l.material.color.setHex(0x208CFF);
        l.children.forEach(glow => glow.material.color.setHex(0x208CFF));
      });
    }

    if (cfg.scale) actorMesh.scale.multiplyScalar(cfg.scale);
    const visual = new THREE.Group();
    [...actorMesh.children].forEach(child => visual.add(child));
    actorMesh.add(visual);
    actorMesh.userData.body = visual;
    // Glow sprites are presentation only, never collision geometry.
    actorMesh.updateMatrixWorld(true);
    const physicalBounds = new THREE.Box3();
    actorMesh.traverse(part => {
      if (!part.isMesh) return;
      part.geometry.computeBoundingBox();
      physicalBounds.union(part.geometry.boundingBox.clone().applyMatrix4(part.matrixWorld));
    });
    const modelSize = physicalBounds.getSize(new THREE.Vector3());
    const halfLength = modelSize.z / 2;
    // Add badge above roof
    const badgeLabel = cfg.siren ? 'Маячок + сирена' : cfg.badge || (
      cfg.name ? (
        cfg.name.includes('Трамвай А') ? 'А' :
        cfg.name.includes('Трамвай Б') ? 'Б' :
        cfg.name.includes('Трамвай') ? 'Трамвай' :
        cfg.name.includes('Автобус') ? 'Автобус' :
        cfg.name.includes('Фургон') ? 'Фургон' :
        cfg.name.includes('Грузовик') ? 'Грузовик' :
        cfg.name.includes('Повозка') ? 'Повозка' :
        cfg.name.includes('Спец') ? 'Спец' :
        cfg.name.includes('Мотоцикл') ? 'Мото' :
        cfg.name.includes('Велосипед') ? 'Вело' :
        cfg.name.includes('Пешеход') ? 'Пешеход' :
        cfg.name.includes('Встреч') ? 'Встречный' :
        'Авто'
      ) : 'Авто'
    );
    const badge = createActorBadge(badgeLabel, cfg.color || BRAND.accent);
    badge.position.y = badgeHeight;
    actorMesh.add(badge);
    actorMesh.userData.badge = badge;
    if(cfg.hideBadge)badge.visible=false;
    actorMesh.traverse(obj => { obj.userData.actor = true; });
    // Every motor vehicle has indicators: junction traffic signals its
    // targetAction exactly as the ticket picture shows it.
    if (cfg.blinker || cfg.maneuver || !['pedestrian', 'cyclist', 'cart', 'train'].includes(cfg.type)) {
      // Turn signals readable from the chase camera, on both sides; which side
      // blinks (if any) follows the actor's manoeuvre plan.
      const k = actorMesh.scale.x;
      // At the very corners of the body, poking out a little: on a tall
      // truck or bus a lamp set inside the outline hides under the cargo box
      // or roof as seen by the chase camera.
      // Each model knows where its head and tail lamps are (lampSpec, model
      // units): the indicators sit just outboard of them, on the body — not
      // at the outline of wheels, mirrors or a trailer hanging in the air.
      const spec = actorMesh.userData.lampSpec;
      const lampAt = (side, end) => {
        if (!spec) return [side * (modelSize.x / 2 - 0.02) / k, 0.85 / k, end * (halfLength + 0.04) / k];
        const l = end > 0 ? spec.front : spec.rear;
        return [side * (spec.single ? 0.22 : l.x + 0.2), l.y, l.z + end * 0.06];
      };
      const lamps = side => [-1, 1].map(end => {
        const lamp = new THREE.Mesh(new THREE.BoxGeometry(0.16, 0.14, 0.12), new THREE.MeshBasicMaterial({ color: 0xFFB21C }));
        lamp.position.set(...lampAt(side, end));
        lamp.visible = false;
        window.PDD_VEHICLES.addGlow(lamp, 0xFFB21C, 1.1);
        actorMesh.userData.body.add(lamp);
        return lamp;
      });
      actorMesh.userData.blinkerLamps = { left: lamps(1), right: lamps(-1) };
      actorMesh.userData.blinkerSide = cfg.blinker || null;
    }
    return { actorMesh, halfLength, halfWidth: modelSize.x / 2 };
  }

  function buildRoundaboutSegment(startZ, situation, incomingRoad = null) {
    const spec = routeSpec(situation);
    situation = { ...situation, ...(spec.overrides || {}) };
    const intentions = { straight: 'Вы прямо', left: 'Вы налево', right: 'Вы направо', uturn: 'Вы на разворот' };
    situation.legend = [{ label: intentions[spec.maneuver] || 'Вы на круг', color: '#ED4621' },
      ...(situation.actorsConfig || []).map(a => ({ label: a.name, color: a.color || '#0574F8' }))];
    const seg = new THREE.Group();
    const roadWidth = 8.4;
    const intersectionLength = 52;
    const centerZ = startZ + 26;
    const crossStreetLength = 70;

    // The same lawn colour as the roads that meet here: the approach ends and
    // every exit starts in district (state.district + 1). No colour seam.
    const lawn = Math.min((state.district + 1) % DISTRICTS, 2);
    const districtGround = new THREE.Mesh(new THREE.PlaneGeometry(crossStreetLength + SEAM, intersectionLength + SEAM),
      new THREE.MeshLambertMaterial({ color: season().verge[lawn] }));
    districtGround.material.userData.seasonal = 'verge' + lawn;
    districtGround.rotation.x = -Math.PI / 2;
    districtGround.position.set(0, -0.02, centerZ);
    districtGround.receiveShadow = true;
    seg.add(districtGround);

    // Central Island (radius 8.5m)
    const islandCurb = new THREE.Mesh(
      new THREE.CylinderGeometry(8.5, 8.5, 0.2, 48),
      new THREE.MeshLambertMaterial({ color: BRAND.sidewalk })
    );
    islandCurb.position.set(0, 0.1, centerZ);
    islandCurb.receiveShadow = true;
    seg.add(islandCurb);

    const islandLawn = new THREE.Mesh(
      new THREE.CircleGeometry(8.3, 48),
      new THREE.MeshLambertMaterial({ color: season().ground })
    );
    islandLawn.material.userData.seasonal = 'ground';
    islandLawn.rotation.x = -Math.PI / 2;
    islandLawn.position.set(0, 0.205, centerZ);
    islandLawn.receiveShadow = true;
    seg.add(islandLawn);

    // An advertising board in the middle of the island (an invented brand).
    const billboard = createIslandBillboard();
    billboard.position.set(0, 0.2, centerZ);
    seg.add(billboard);

    // Circular Ring Asphalt (inner 8.5m, outer 15.5m)
    // The asphalt runs 6 cm under the raised pavement, whose kerb follows the
    // ring exactly (no step where the entry flares meet it).
    const ringGeo = new THREE.RingGeometry(8.5, 15.56, 160);
    ringGeo.rotateX(-Math.PI / 2);
    const ringAsphalt = new THREE.Mesh(ringGeo, new THREE.MeshLambertMaterial({ color: BRAND.asphalt }));
    ringAsphalt.position.set(0, 0.021, centerZ);
    ringAsphalt.userData.surface = 'road';
    // The ring is road only outside the island (its bounding box covers the
    // island too): like a rounded corner, road outside this circle.
    ringAsphalt.userData.fillet = { center: new THREE.Vector3(0, 0, 0), r: 8.5 };
    ringAsphalt.receiveShadow = true;
    seg.add(ringAsphalt);

    // 4 Straight approach roads connecting to the ring
    const southLen = (intersectionLength / 2) - 14.5;
    const southAsphalt = new THREE.Mesh(new THREE.PlaneGeometry(roadWidth, southLen + SEAM), new THREE.MeshLambertMaterial({ color: BRAND.asphalt }));
    southAsphalt.rotation.x = -Math.PI / 2;
    southAsphalt.position.set(0, 0.02, startZ + southLen / 2);
    southAsphalt.userData.surface = 'road';
    southAsphalt.receiveShadow = true;
    seg.add(southAsphalt);

    const northAsphalt = new THREE.Mesh(new THREE.PlaneGeometry(roadWidth, southLen + SEAM), new THREE.MeshLambertMaterial({ color: BRAND.asphalt }));
    northAsphalt.rotation.x = -Math.PI / 2;
    northAsphalt.position.set(0, 0.02, centerZ + 14.5 + southLen / 2);
    northAsphalt.userData.surface = 'road';
    northAsphalt.receiveShadow = true;
    seg.add(northAsphalt);

    const westLen = (crossStreetLength / 2) - 14.5;
    const westAsphalt = new THREE.Mesh(new THREE.PlaneGeometry(westLen + SEAM, roadWidth), new THREE.MeshLambertMaterial({ color: BRAND.asphalt }));
    westAsphalt.rotation.x = -Math.PI / 2;
    westAsphalt.position.set(-(14.5 + westLen / 2), 0.02, centerZ);
    westAsphalt.userData.surface = 'road';
    westAsphalt.receiveShadow = true;
    seg.add(westAsphalt);

    const eastAsphalt = new THREE.Mesh(new THREE.PlaneGeometry(westLen + SEAM, roadWidth), new THREE.MeshLambertMaterial({ color: BRAND.asphalt }));
    eastAsphalt.rotation.x = -Math.PI / 2;
    eastAsphalt.position.set(14.5 + westLen / 2, 0.02, centerZ);
    eastAsphalt.userData.surface = 'road';
    eastAsphalt.receiveShadow = true;
    seg.add(eastAsphalt);

    // Pavements: one raised slab per quadrant runs along both road arms and
    // round the outside of the ring. Where an arm meets the ring the kerb
    // flares on a 5 m radius (no sharp corner to clip when entering), and the
    // asphalt in that flare is road for the kerb check up to the exact curve.
    const swW = 3.2, Ro = 15.5, rf = 5, ringPave = 18.7;
    const Fz = Math.sqrt((Ro + rf) ** 2 - (4.2 + rf) ** 2), F = [4.2 + rf, Fz];
    const T2 = [F[0] * Ro / (Ro + rf), F[1] * Ro / (Ro + rf)];
    const phi2 = Math.atan2(-F[1], -F[0]);
    const flare = (radius, n = 12) => Array.from({ length: n + 1 }, (_, i) => {
      const a = phi2 + (-Math.PI - phi2) * i / n; // from the ring round to the arm kerb
      return [F[0] + radius * Math.cos(a), F[1] + radius * Math.sin(a)];
    });
    // The raised pavement is sampled finely along the ring, so no sliver of
    // mismatched polygon edges shows along the kerb.
    const ringArc = (from, to, n = 48, radius = Ro) => Array.from({ length: n + 1 }, (_, i) => {
      const a = from + (to - from) * i / n; return [radius * Math.sin(a), radius * Math.cos(a)];
    });
    const swap = pts => pts.map(([x, z]) => [z, x]);
    const thetaF = Math.atan2(F[0], F[1]);
    const shapeOf = pts => { const sh = new THREE.Shape(); sh.moveTo(...pts[0]); pts.slice(1).forEach(q => sh.lineTo(...q)); sh.closePath(); return sh; };
    for (let quadrant = 0; quadrant < 4; quadrant++) {
      const lenZ = quadrant % 2 === 0 ? intersectionLength / 2 : crossStreetLength / 2;
      const lenX = quadrant % 2 === 0 ? crossStreetLength / 2 : intersectionLength / 2;
      const a0 = Math.asin(7.4 / ringPave);
      const outer = Array.from({ length: 49 }, (_, i) => { const a = a0 + (Math.PI / 2 - 2 * a0) * i / 48; return [ringPave * Math.sin(a), ringPave * Math.cos(a)]; });
      // Kerb from the x-arm (Fz, 4.2) round its flare, along the ring and
      // round the other flare to the z-arm (4.2, Fz).
      const kerb = [...[...swap(flare(rf))].reverse(), ...ringArc(Math.PI / 2 - thetaF, thetaF, 48, Ro).slice(1, -1), ...flare(rf)];
      const pave = [[4.2, lenZ + SEAM], [7.4, lenZ + SEAM], ...outer, [lenX + SEAM, 7.4], [lenX + SEAM, 4.2], ...kerb];
      const geo = new THREE.ExtrudeGeometry(shapeOf(pave), { depth: 0.18, bevelEnabled: false });
      geo.rotateX(Math.PI / 2);
      const slab = new THREE.Mesh(geo, new THREE.MeshLambertMaterial({ color: BRAND.sidewalk, side: THREE.DoubleSide }));
      slab.rotation.y = quadrant * Math.PI / 2;
      slab.position.set(0, 0.18, centerZ);
      seg.add(slab);
      // Asphalt in both flares of this quadrant.
      const flareRoad = [[4.2, Fz], [4.2, Math.sqrt(Ro * Ro - 4.2 * 4.2)], ...ringArc(Math.asin(4.2 / Ro), thetaF).slice(1), ...flare(rf).slice(1)];
      for (const pts of [flareRoad, swap(flareRoad)]) {
        const g = new THREE.ShapeGeometry(shapeOf(pts)); g.rotateX(Math.PI / 2);
        const m = new THREE.Mesh(g, new THREE.MeshLambertMaterial({ color: BRAND.asphalt, side: THREE.DoubleSide }));
        m.rotation.y = quadrant * Math.PI / 2; m.position.set(0, 0.021, centerZ);
        m.userData.surface = 'road';
        const c = pts === flareRoad ? F : [F[1], F[0]];
        m.userData.fillet = { center: new THREE.Vector3(c[0], 0, c[1]), r: rf };
        seg.add(m);
      }
    }
    const armEdgeStart = Fz; // the arms' edge lines start where the flare ends
    // Edge line round each quadrant: along both flares and the ring's kerb,
    // joining the arms' edge lines (which end at the flares) without a gap.
    const edgePath = (dFlare, dRing) => [...[...swap(flare(rf + dFlare))].reverse(),
      ...ringArc(Math.PI / 2 - thetaF, thetaF, 48, Ro - dRing).slice(1, -1), ...flare(rf + dFlare)];
    const edgeMat = new THREE.MeshBasicMaterial({ color: BRAND.asphaltMarking });
    for (let quadrant = 0; quadrant < 4; quadrant++) {
      const a = edgePath(0.175, 0.175), b = edgePath(0.325, 0.325), quads = [];
      for (let i = 1; i < a.length; i++) quads.push([a[i - 1], a[i], b[i], b[i - 1]]);
      const line = addBakedQuads(seg, quads, 0.028, edgeMat);
      line.rotation.y = quadrant * Math.PI / 2; line.position.z = centerZ; line.userData.roadMarking = true;
    }

    // Markings
    const markingMat = new THREE.MeshBasicMaterial({ color: BRAND.asphaltMarking });

    for (let a = 0; a < 2 * Math.PI; a += 0.28) {
      const dash = new THREE.Mesh(new THREE.PlaneGeometry(0.18, 1.8), markingMat);
      dash.geometry.rotateX(-Math.PI / 2);
      dash.position.set(12.0 * Math.sin(a), 0.028, centerZ + 12.0 * Math.cos(a));
      dash.rotation.y = a + Math.PI / 2;
      dash.userData.roadMarking = true;
      seg.add(dash);
    }

    // Approach markings stop before the circular carriageway; edge lines
    // continue to the adjoining straight segments without a bare seam.
    for (let arm = 0; arm < 4; arm++) {
      const longitudinal = arm % 2 === 0;
      const sign = arm < 2 ? 1 : -1;
      const end = longitudinal ? intersectionLength / 2 : crossStreetLength / 2;
      for (const edge of [-3.95, 3.95]) {
        const length = end - armEdgeStart + SEAM;
        addFlatPlane(seg, longitudinal ? 0.15 : length,
          longitudinal ? length : 0.15,
          longitudinal ? edge : sign * (armEdgeStart + end) / 2,
          centerZ + (longitudinal ? sign * (armEdgeStart + end) / 2 : edge), 0.028, markingMat);
      }
      for (let distance = 19; distance < end - 1; distance += 5) {
        addFlatPlane(seg, longitudinal ? 0.18 : 2,
          longitudinal ? 2 : 0.18,
          longitudinal ? 0 : sign * distance,
          centerZ + (longitudinal ? sign * distance : 0), 0.028, markingMat);
      }
    }

    // The ticket owns priority evidence; do not invent a yield sign for
    // roundabouts whose source scene contains only sign 4.3.
    (situation.signs || []).forEach((entry, index) => {
      const sign = createRoadSign(entry.code);
      sign.position.set(roadWidth / 2 + 1.2, 0, centerZ - 18.5 - index * 2.5);
      seg.add(sign);
    });

    // Place Actors
    const actorsInScene = [];
    (situation.actorsConfig || []).forEach(cfg => {
      const { actorMesh, halfLength, halfWidth } = createActorMesh(cfg);
      if (cfg.side === 'ring' || cfg.roundabout) {
        const ringRadius = cfg.ringRadius || 12.0;
        const ringAngle = cfg.ringAngle !== undefined ? cfg.ringAngle : (cfg.id.includes('moto') ? 0.8 : 2.1);
        actorMesh.position.set(ringRadius * Math.sin(ringAngle), 0, centerZ + ringRadius * Math.cos(ringAngle));
        actorMesh.rotation.y = ringAngle + Math.PI / 2;
      } else if (cfg.side === 'cross_left') {
        actorMesh.position.set(-18, 0, centerZ - 2.05);
        actorMesh.rotation.y = Math.PI / 2;
      } else if (cfg.side === 'cross_right') {
        actorMesh.position.set(18, 0, centerZ + 2.05);
        actorMesh.rotation.y = -Math.PI / 2;
      } else {
        actorMesh.position.set(0, 0, centerZ);
      }
      seg.add(actorMesh);
      actorsInScene.push({ actorMesh, mesh: actorMesh, config: cfg, halfLength, halfWidth, initialPos: actorMesh.position.clone() });
    });

    registerRoadSegment(seg);
    applySceneEdits(seg, situation.id, centerZ);
    actorsInScene.forEach(a => {
      a.initialPos = a.mesh.position.clone();
      a.viewBounds = new THREE.Box3().setFromObject(a.mesh);
    });
    state.roadSegments.push(seg);

    const intersectionData = {
      seg,
      startZ,
      centerZ,
      stopZ: centerZ - 17.5,
      situation,
      actors: actorsInScene,
      trafficLight: null
    };
    state.intersections.push(intersectionData);
    ensureTraffic(intersectionData);

    const guide = new THREE.Group();
    const action = spec.maneuver || 'right';
    let guidePoints;
    if (action === 'right') {
      guidePoints = [[-1.8, -18], [-3.5, -14], [-7.5, -10], [-12, -4], [-18, -1.8], [-24, -1.8]];
    } else if (action === 'straight') {
      guidePoints = [[-1.8, -18], [-4.0, -14], [-9.5, -6], [-10.5, 0], [-8.5, 8], [-4.0, 14], [-1.8, 18], [-1.8, 24]];
    } else {
      guidePoints = [[-1.8, -18], [-4.0, -14], [-9.5, -6], [-10.5, 0], [-8.5, 8], [0, 11.5], [8.5, 8], [14, 4], [18, 1.8], [24, 1.8]];
    }
    const guidePaths = [curve(guidePoints.map(([x, z]) => new THREE.Vector3(x, 0.12, centerZ + z)))];
    createRouteGuide(guidePaths).children.slice().forEach(part => guide.add(part));
    seg.add(guide); guide.visible = false;
    intersectionData.guide = guide;

    intersectionData.previews = {};
    for (const [direction, yaw, x, z] of [
      ['straight', 0, 0, startZ + intersectionLength],
      ['left', Math.PI / 2, crossStreetLength / 2, centerZ],
      ['right', -Math.PI / 2, -crossStreetLength / 2, centerZ],
    ]) {
      const extension = buildStraightSegment(0, 200, true, (state.district + 1) % DISTRICTS, null, direction === 'straight' ? 0 : 30);
      extension.rotation.y = yaw;
      extension.position.set(x, 0, z);
      seg.add(extension);
      intersectionData.previews[direction] = extension;
    }
    if (incomingRoad) {
      scene.updateMatrixWorld(true);
      const world = incomingRoad.matrixWorld.clone();
      seg.add(incomingRoad);
      incomingRoad.matrix.copy(world);
      world.decompose(incomingRoad.position, incomingRoad.quaternion, incomingRoad.scale);
      state.roadSegments = state.roadSegments.filter(s => s !== incomingRoad);
      intersectionData.previews.uturn = incomingRoad;
    }

    refreshRoadBounds();
    return intersectionLength;
  }

  function buildIntersectionSegment(startZ, situation, incomingRoad = null) {
    let spec = routeSpec(situation);
    situation = { ...situation, ...(spec.overrides || {}) };
    if(situation.pedestrianCount) {
      const count=situation.pedestrianCount.min+Math.floor(Math.random()*(situation.pedestrianCount.max-situation.pedestrianCount.min+1));
      const actors=[],yieldTo=[...spec.yieldTo];
      for(const cfg of situation.actorsConfig||[]) {
        if(cfg.type!=='pedestrian'){actors.push(cfg);continue;}
        const sx=cfg.side==='crosswalk_right'?1:-1,base=(situation.mainWidth||8.4)/2+1.9;
        for(let i=0;i<count;i++) {
          const id=i?cfg.id+'_'+(i+1):cfg.id;
          actors.push({...cfg,id,hideBadge:i>0,concurrentWith:[...(cfg.concurrentWith||[]),...Array.from({length:count},(_,j)=>j?cfg.id+'_'+(j+1):cfg.id).filter(other=>other!==id)],position:[sx*(base+(i-(count-1)/2)*1.25),.18,-(situation.crossWidth||8.4)/2-1.4]});
          if(i&&spec.yieldTo.includes(cfg.id))yieldTo.push(id);
        }
      }
      situation.actorsConfig=actors;spec={...spec,yieldTo};situation.resolvedRoute=spec;
    }
    if (situation.geometry === 'roundabout') return buildRoundaboutSegment(startZ, situation, incomingRoad);
    const intentions = { straight: 'Вы прямо', left: 'Вы налево', right: 'Вы направо', uturn: 'Вы на разворот' };
    situation.legend = [{ label: intentions[spec.maneuver], color: '#ED4621' },
      ...(situation.actorsConfig || []).map(a => ({ label: a.name, color: a.color || '#0574F8' }))];
    const seg = new THREE.Group();
    const roadWidth = 8.4;
    const intersectionLength = 52;
    const centerZ = startZ + 26;
    const crossStreetLength = 70;
    const tJunction = situation.geometry === 't_no_straight';
    const dirtApproach = situation.geometry === 'dirt_approach';
    // Wide cross street (situation.crossWidth, or a dual carriageway for
    // 'divided_road'): full width at the junction, narrowing smoothly to the
    // ordinary 8.4 m road over |x| 18...33 so it meets the exit roads with no
    // step. Trams keep the inner lanes, cars the outer ones.
    const divided = situation.geometry === 'divided_road';
    const crossW = situation.crossWidth || (divided ? 20.8 : roadWidth);
    const wide = crossW > roadWidth + 0.01;
    const medianHalf = divided ? 2 : 0;
    const narrow = x => THREE.MathUtils.smoothstep(Math.abs(x), 18, 33);
    const halfW = x => crossW / 2 + (roadWidth / 2 - crossW / 2) * narrow(x);
    // The island keeps its width to its round end at 28 m.
    const medHalf = x => Math.abs(x) <= 26 ? medianHalf : 0;
    const laneW = (crossW / 2 - medianHalf) / 2;
    // The same for the main street (situation.mainWidth): e.g. a tram in the
    // inner oncoming lane with a car beside it, both clear of the kerb.
    const mainW = situation.mainWidth || roadWidth;
    const wideMain = mainW > roadWidth + 0.01 && !tJunction;
    const halfM = z => mainW / 2 + (roadWidth / 2 - mainW / 2) * THREE.MathUtils.smoothstep(Math.abs(z - centerZ), 13, 25);
    const kerbX = mainW / 2, kerbZ = crossW / 2; // kerb lines at the junction itself
    // The same lawn colour as the roads that meet here: the approach ends and
    // every exit starts in district (state.district + 1). No colour seam.
    const lawn = Math.min((state.district + 1) % DISTRICTS, 2);
    const districtGround = new THREE.Mesh(new THREE.PlaneGeometry(crossStreetLength + SEAM, intersectionLength + SEAM),
      new THREE.MeshLambertMaterial({ color: season().verge[lawn] }));
    districtGround.material.userData.seasonal = 'verge' + lawn;
    districtGround.rotation.x = -Math.PI / 2;
    districtGround.position.set(0, -0.02, centerZ);
    districtGround.receiveShadow = true;
    seg.add(districtGround);

    // Main longitudinal asphalt
    const mainAsphaltLength = tJunction ? intersectionLength / 2 + roadWidth / 2 + SEAM : intersectionLength + 2 * SEAM;
    const mainAsphalt = new THREE.Mesh(
      new THREE.PlaneGeometry(roadWidth, mainAsphaltLength),
      new THREE.MeshLambertMaterial({ color: BRAND.asphalt })
    );
    mainAsphalt.rotation.x = -Math.PI / 2;
    mainAsphalt.position.set(0, 0.02, tJunction ? startZ + mainAsphaltLength / 2 : centerZ);
    mainAsphalt.receiveShadow = true;
    seg.add(mainAsphalt);
    if (wideMain) {
      mainAsphalt.visible = false; mainAsphalt.scale.set(0.0001, 0.0001, 1);
      const mat = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
      for (let z = startZ - SEAM; z < startZ + intersectionLength + SEAM - 1e-6; z += 1.5) {
        const m = addRibbon(seg, z, Math.min(z + 1.5, startZ + intersectionLength + SEAM), q => -halfM(q), q => halfM(q), 0.02, mat, 0.75);
        m.userData.surface = 'road'; m.receiveShadow = true;
      }
    }

    // Crossing street asphalt (extends left and right across entire screen)
    const crossAsphalt = new THREE.Mesh(
      new THREE.PlaneGeometry(dirtApproach ? (crossStreetLength + roadWidth) / 2 + SEAM : crossStreetLength + 2 * SEAM, roadWidth),
      new THREE.MeshLambertMaterial({ color: BRAND.asphalt })
    );
    crossAsphalt.rotation.x = -Math.PI / 2;
    crossAsphalt.position.set(0, 0.021, centerZ);
    if (dirtApproach) crossAsphalt.position.x = -(crossStreetLength - roadWidth) / 4;
    crossAsphalt.receiveShadow = true;
    if (wide) {
      // Tapered: short chunks keep each drivable bounding box tight.
      crossAsphalt.visible = false; crossAsphalt.scale.set(0.0001, 0.0001, 1);
      addRibbonX(seg, -crossStreetLength / 2 - SEAM, crossStreetLength / 2 + SEAM,
        x => centerZ - halfW(x), x => centerZ + halfW(x), 0.021, new THREE.MeshLambertMaterial({ color: BRAND.asphalt }), 1.5)
        .forEach(m => { m.userData.surface = 'road'; m.receiveShadow = true; });
    }
    seg.add(crossAsphalt);

    const markingMat = new THREE.MeshBasicMaterial({ color: BRAND.asphaltMarking });

    if (dirtApproach) {
      const dirtArm = new THREE.Group();
      addDirtSurface(dirtArm, -3.2, (crossStreetLength - roadWidth) / 2 + SEAM);
      dirtArm.rotation.y = Math.PI / 2;
      dirtArm.position.set(roadWidth / 2, 0, centerZ);
      seg.add(dirtArm);
    }

    // 'motorway_merge' (ticket 2.15) needs no extra geometry: the 5.1 sign
    // of the ticket marks the player's road. A separate acceleration lane
    // used to lie under the pavement (a black strip behind the kerb) together
    // with a second, duplicate 5.1 sign.

    if (situation.geometry === 'divided_road') {
      const medianW = 4.0;
      // The median separates the carriageways and tapers to a point where
      // they merge into the ordinary exit road.
      for (const side of (situation.noRight ? [1] : [-1, 1])) {
        // A kerbed island with round ends, its nose clear of the main road's
        // kerb line; a car cannot drive across it (as over any kerb).
        addRoundIsland(seg, side * (roadWidth / 2 + 0.4), side * 28, medianW / 2, centerZ);
      }
      const medianTL = createTrafficLight('red');
      medianTL.visible = situation.medianSignals !== false;
      // On the median's nose, inside its kerb (it used to stand 0.4 m out on
      // the carriageway).
      medianTL.position.set(roadWidth / 2 + 1.6, 0, centerZ + medianW / 2 - 0.6);
      medianTL.rotation.y = -Math.PI / 2;
      seg.add(medianTL);
      seg.userData.medianTrafficLight = medianTL;
      if (situation.hasMedianStopLine) {
        const medStop = new THREE.Mesh(new THREE.PlaneGeometry(roadWidth / 2, 0.45), markingMat);
        medStop.rotation.x = -Math.PI / 2;
        medStop.position.set(roadWidth / 4, 0.028, centerZ + medianW / 2);
        medStop.userData.medianStopLine = true;
        seg.add(medStop);
        const stop616 = createRoadSign('6.16');
        stop616.position.set(roadWidth / 2 + 0.6, 0, centerZ + medianW / 2 - 1.2);
        stop616.rotation.y = -Math.PI / 2;
        seg.add(stop616);
      }
    }

    if(situation.geometry==='three_carriageways') {
      // Three equal carriageways (8.27 m, two lanes each) between two 2.2 m
      // islands with round ends, as in the source photograph.
      // They end at 20 m, where the carriageways start to merge into the exit road.
      for(const side of [-1,1])for(const laneZ of [-THREE_ISLAND_Z,THREE_ISLAND_Z]) addRoundIsland(seg,side*4.6,side*20,1.1,centerZ,laneZ);
    }
    if(situation.geometry === 'divided_main') {
      for(const side of [-1,1]) {
        const zs=[];for(let d=7.4;d<25;d+=.75)zs.push(centerZ+side*d);zs.push(centerZ+side*26);
        const half=z=>2*(1-THREE.MathUtils.smoothstep(Math.abs(z-centerZ),13,25));
        const slab=extrudedStripZ(zs,z=>-half(z),half,.18,new THREE.MeshLambertMaterial({color:BRAND.sidewalk}));
        slab.userData.noRoad=p=>Math.abs(p.z-centerZ)>=7.4&&Math.abs(p.x)<half(p.z)-.05;seg.add(slab);
        const lawnMat=new THREE.MeshLambertMaterial({color:season().ground});lawnMat.userData.seasonal='ground';
        const lo=Math.min(...zs),hi=Math.max(...zs);addRibbon(seg,lo,hi,z=>-Math.max(0,half(z)-.18),z=>Math.max(0,half(z)-.18),.186,lawnMat);
      }
      const farLight=createTrafficLight('red');farLight.position.set(-kerbX-2,0,centerZ+kerbZ+1.2);farLight.rotation.y=Math.PI/2;seg.add(farLight);seg.userData.medianTrafficLight=farLight;
      if(situation.hasMedianStopLine) {
        const lineX=situation.medianStopX??kerbX+.6;
        const line=addFlatPlane(seg,.45,4.2,-lineX,centerZ+2.1,.03,markingMat);line.userData.medianStopLine=true;
        const plate=createRoadSign('6.16');plate.position.set(-kerbX-2,-1.05,centerZ+kerbZ+1.2);plate.rotation.y=-Math.PI/2;
        plate.children.filter(o=>o.geometry?.type==='CylinderGeometry').forEach(o=>o.visible=false);seg.add(plate);
      }
    }

    // Sidewalks on all 4 corners
    const swW = 3.2;
    const cornerL = (crossStreetLength - roadWidth) / 2;

    // Corners run along the cross street only, from the outer edge of the
    // main-street pavement outwards: no coplanar overlap with those pavements.
    // Pavements keep their width and follow a widening kerb: the rounded
    // corner pieces (addCornerFillet, a pavement-width square) then meet them
    // exactly — narrowing them left the corners sticking out.
    const paveOuter = half => half + swW;
    // Along a slanting kerb (a street widening or narrowing) the pavement's
    // width across it stays swW: measured along the street it has to be
    // wider by 1/cos of the slant, or the pavement looks pinched there.
    const slantOuter = (half, v) => {
      const d = (half(v + 0.05) - half(v - 0.05)) / 0.1;
      return half(v) + swW * Math.sqrt(1 + d * d);
    };
    // Strips sampled every metre must still end exactly at their ends: a
    // last sample short of the end left a gap to the next piece.
    const samples = (from, to, step = 1) => {
      const out = [];
      for (let v = from; v < to - 1e-6; v += step) out.push(v);
      out.push(to);
      return out;
    };
    const cornerStart = paveOuter(kerbX), crossOuter0 = paveOuter(kerbZ);
    const cornerW = crossStreetLength / 2 - cornerStart + SEAM, cornerX = cornerStart - 0.03 + cornerW / 2;
    const corner = (sx, sz) => {
      if (dirtApproach && sx > 0) return;
      if (wide) {
        // The pavement follows the tapering kerb.
        const xs = samples(cornerStart - 0.03, crossStreetLength / 2 + SEAM).map(x => sx * x);
        const slab = extrudedStrip(xs, x => sz < 0 ? -slantOuter(halfW, x) : halfW(x), x => sz < 0 ? -halfW(x) : slantOuter(halfW, x), 0.18,
          new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
        slab.position.z = centerZ; seg.add(slab); return slab;
      }
      const box = new THREE.Mesh(new THREE.BoxGeometry(cornerW, 0.18, swW), new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
      box.position.set(sx * cornerX, 0.09, centerZ + sz * (roadWidth / 2 + swW / 2));
      seg.add(box); return box;
    };
    corner(-1, -1); corner(1, -1);
    if (!tJunction) { corner(-1, 1); corner(1, 1); }

    // Main street entrance sidewalks
    if (wideMain) {
      // Pavements follow the widening main street (entrance and exit).
      const pave = () => new THREE.MeshLambertMaterial({ color: BRAND.sidewalk });
      for (const side of [-1, 1]) for (const [a, b] of [[startZ - SEAM, centerZ - crossOuter0], [centerZ + crossOuter0, startZ + intersectionLength + SEAM]]) {
        const zs = samples(a, b);
        const slab = extrudedStripZ(zs, z => side < 0 ? -slantOuter(halfM, z) : halfM(z), z => side < 0 ? -halfM(z) : slantOuter(halfM, z), 0.18, pave());
        seg.add(slab);
      }
    }
    // Main pavements stop a pavement-width short of the cross street: the
    // square corner itself is the rounded piece from addCornerFillet.
    const entLen = intersectionLength / 2 - crossOuter0 + SEAM, exitLen = entLen;
    const swMainL = new THREE.Mesh(new THREE.BoxGeometry(swW, 0.18, entLen), new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
    swMainL.position.set(-(roadWidth / 2 + swW / 2), 0.09, startZ - SEAM + entLen / 2);
    if (!wideMain) seg.add(swMainL);

    const swMainR = new THREE.Mesh(new THREE.BoxGeometry(swW, 0.18, entLen), new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
    swMainR.position.set(roadWidth / 2 + swW / 2, 0.09, startZ - SEAM + entLen / 2);
    if (!wideMain) seg.add(swMainR);

    if (tJunction) {
      // One slab spans the whole far side. Combining two corner pieces with a
      // narrow road-width cap left visible holes at both former kerbs.
      const cap = new THREE.Mesh(new THREE.BoxGeometry(crossStreetLength + 2 * SEAM, 0.18, swW),
        new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
      cap.position.set(0, 0.09, centerZ + roadWidth / 2 + swW / 2);
      cap.userData.tJunctionSidewalk = true;
      seg.add(cap);
    } else {
      // Main street exit sidewalks
      const swMainL_exit = new THREE.Mesh(new THREE.BoxGeometry(swW, 0.18, exitLen), new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
      swMainL_exit.position.set(-(roadWidth / 2 + swW / 2), 0.09, startZ + intersectionLength + SEAM - exitLen / 2);
      if (!wideMain) seg.add(swMainL_exit);

      const swMainR_exit = new THREE.Mesh(new THREE.BoxGeometry(swW, 0.18, exitLen), new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
      swMainR_exit.position.set(roadWidth / 2 + swW / 2, 0.09, startZ + intersectionLength + SEAM - exitLen / 2);
      if (!wideMain) seg.add(swMainR_exit);
    }

    // Markings

    // Four continuous approaches. Edges join the adjoining straight roads,
    // but all longitudinal paint stops before the crossings (no zebra overlap).
    function approachLine(x, from, to, width, yaw) {
      const line = new THREE.Mesh(new THREE.PlaneGeometry(width, to - from), markingMat);
      line.rotation.x = -Math.PI / 2;
      const local = new THREE.Vector3(x, 0.032, (from + to) / 2);
      local.applyAxisAngle(new THREE.Vector3(0, 1, 0), yaw);
      line.position.copy(local); line.position.z += centerZ;
      line.rotation.z = yaw;
      line.userData.roadMarking = true;
      seg.add(line);
    }
    // One-way cross street (situation.oneWay = 'to_right' | 'to_left', as
    // seen by the player): no solid centre line 1.1 on it, only the lane
    // divider 1.5 between two lanes of the same direction.
    const oneWay = situation.oneWay || null;
    for (const [yaw, end] of [[0, 26], [Math.PI, 26], [Math.PI / 2, 35], [-Math.PI / 2, 35]]) {
      if (tJunction && yaw === 0) continue;
      const crossArm = Math.abs(Math.sin(yaw)) > 0.5;
      if (dirtApproach && yaw === Math.PI / 2) continue;
      if ((wide && crossArm) || (wideMain && !crossArm)) continue; // drawn along the taper below
      const from = crossArm ? kerbX + 3.4 : kerbZ + 3.4, shift = from - 7.6;
      for (const edge of [-1, 1]) approachLine(edge * (roadWidth / 2 - 0.25), from, end, 0.15, yaw);
      if (oneWay && crossArm) { for (let z = 8; z < end; z += 5) approachLine(0, z, Math.min(z + 2, end), 0.15, yaw); continue; }
      approachLine(0, from, 16 + shift, 0.18, yaw);
      // Transition back to the same 2m / 3m dashed centre as the open road.
      for (let z = 18 + shift; z < end; z += 5) approachLine(0, z, Math.min(z + 2, end), 0.18, yaw);
    }
    if (wideMain) {
      // Main-street paint along its widening: kerb edges, a solid centre
      // near the junction, lane dividers where there are two lanes a side.
      const lineZ = (a, b, xc, w) => { const m = addRibbon(seg, a, b, z => xc(z) - w / 2, z => xc(z) + w / 2, 0.032, markingMat, 0.75); return m; };
      for (const sz of [-1, 1]) {
        const span = (a, b) => sz < 0 ? [centerZ - b, centerZ - a] : [centerZ + a, centerZ + b];
        for (const sx of [-1, 1]) {
          lineZ(...span(kerbZ + 3.4, 26 + SEAM), z => sx * (halfM(z) - 0.25), 0.15);
          for (const divider of (situation.mainLaneDividers || [mainW / 4]))
            for (let d = kerbZ + 3.4; d < 20; d += 5) lineZ(...span(d, Math.min(d + 2, 20)), z => sx * divider * halfM(z) / (mainW / 2), 0.15);
        }
        lineZ(...span(kerbZ + 3.4, 17), () => 0, 0.18);
        for (let d = 19; d < 26; d += 5) lineZ(...span(d, Math.min(d + 2, 26)), () => 0, 0.18);
        if (situation.mainCentre === 'double') {
          for (const x of [-0.12, 0.12]) lineZ(...span(kerbZ + 3.4, 17), () => x, 0.13);
        }
      }
    }
    if (wide) {
      // Cross-street paint following the taper: kerb edges, the median's
      // edges or a solid centre line, lane dividers that end where the lanes
      // merge, then the open road's dashed centre.
      const line = (from, to, zc, w) => addRibbonX(seg, from, to, x => centerZ + zc(x) - w / 2, x => centerZ + zc(x) + w / 2, 0.032, markingMat, 1.5);
      const dashes = (from, to, zc, w) => { for (let x = from; x < to; x += 5) line(x, Math.min(x + 2, to), zc, w); };
      const threeWays = situation.geometry === 'three_carriageways';
      for (const sx of [-1, 1]) {
        const span = (a, b) => sx < 0 ? [-b, -a] : [a, b];
        for (const sz of [-1, 1]) {
          line(...span(kerbX + 3.4, 35 + SEAM), x => sz * (halfW(x) - 0.25), 0.15);
          if (divided) line(...span(kerbX + 3.4, 26), x => sz * (medianHalf + 0.25), 0.15);
          // Lane divider in the middle of each outer carriageway.
          if (threeWays) dashes(...span(kerbX + 3.4, 18), x => sz * (THREE_ISLAND_Z + 1.1 + halfW(x)) / 2, 0.15);
          else dashes(...span(kerbX + 3.4, 24), x => sz * (medHalf(x) + halfW(x)) / 2, 0.15);
        }
        if (divided) dashes(...span(30, 35), () => 0, 0.18);
        else { line(...span(kerbX + 3.4, 22), () => 0, 0.18); dashes(...span(24, 35), () => 0, 0.18); }
      }
    }
    if (tJunction) {
      // The far edge of the through road continues across the closed arm.
      // The two horizontal approach pieces stop 7.6 m from the centre, so
      // bridge exactly that gap without overlapping or z-fighting them.
      const edgeBridge = new THREE.Mesh(new THREE.PlaneGeometry(15.2, 0.15), markingMat);
      edgeBridge.rotation.x = -Math.PI / 2;
      edgeBridge.position.set(0, 0.032, centerZ + roadWidth / 2 - 0.25);
      edgeBridge.userData.roadMarking = true;
      edgeBridge.userData.tJunctionEdgeBridge = true;
      seg.add(edgeBridge);
    }

    // Rounded kerbs at every corner, with the edge line following the curve.
    for (const sx of [-1, 1]) for (const sz of tJunction ? [-1] : [-1, 1]) {
      // Fillets bake world X into their vertices; unlike the corner boxes,
      // registerRoadSegment does not mirror them. The right arm is negative X.
      // No road on the right: the kerb and its edge line run straight on.
      if (situation.noRight && sx < 0) continue;
      // The unpaved arm: only the rounded pavement ends, no asphalt corner.
      if (dirtApproach && sx < 0) { addCornerFillet(seg, sx, sz, kerbX, kerbZ, centerZ, markingMat, 3.2, { road: false, line: false }); continue; }
      addCornerFillet(seg, sx, sz, kerbX, kerbZ, centerZ, markingMat);
    }
    if (situation.noRight) addEdgeLineZ(seg, centerZ - kerbZ - 3.4 - SEAM, centerZ + kerbZ + 3.4 + SEAM, () => -kerbX, -1, markingMat);

    // Marking 1.12 belongs only where the source has a signal or STOP sign.
    // Adding it to every unregulated junction invents legally meaningful road
    // evidence which is absent from the exam picture.
    const stopLineZ = centerZ + (situation.stopLineOffset ?? (-crossW / 2 - 4.3));
    const hasStopLine = situation.hasStopLine ?? (!!situation.trafficLights || (situation.signs || []).some(s => s.code === '2.5'));
    if (hasStopLine) {
      const stopLine = new THREE.Mesh(new THREE.PlaneGeometry(kerbX, 0.45), markingMat);
      stopLine.rotation.x = -Math.PI / 2;
      stopLine.position.set(kerbX / 2, 0.027, stopLineZ);
      stopLine.userData.stopLine = true;
      seg.add(stopLine);
    }

    // A crossing is rendered only when it is part of the authored evidence.
    // Pedestrians in 13.1 questions may cross an unmarked road.
    // Pedestrians of the scene cross the side street at a zebra, never across
    // bare asphalt (the answer — 13.1, give way when turning — is the same).
    const walkSides = (situation.actorsConfig || []).filter(a => a.type === 'pedestrian').map(a =>
      a.side === 'crosswalk_left' ? 'left' : a.side === 'crosswalk_right' ? 'right' :
      a.position ? (a.position[0] > 0 ? 'right' : 'left') : null).filter(Boolean);
    if (walkSides.length && !situation.unmarkedCrossings) situation.crosswalks = [...new Set([...(situation.crosswalks || []), ...walkSides])];
    if (situation.crosswalks?.length) {
      const numStripes = 10;
      const stripes = [];
      const addAcrossMain = z => {
        const stripeGeo = new THREE.PlaneGeometry(0.4, 2.6); stripeGeo.rotateX(-Math.PI / 2);
        for (let i = 0; i < numStripes; i++) {
          const stripe = new THREE.Mesh(stripeGeo, markingMat);
          stripe.position.set(-kerbX + 0.45 + i * (2 * kerbX / numStripes), 0.027, z);
          stripes.push(stripe);
        }
      };
      const addAcrossSide = side => {
        for (let i = 0; i < numStripes; i++) {
          const stripe = new THREE.Mesh(new THREE.PlaneGeometry(2.6, 0.4), markingMat);
          stripe.rotation.x = -Math.PI / 2;
          // Merged (baked) geometry is not mirrored by registerRoadSegment,
          // unlike child positions: place the stripes in world X directly.
          stripe.position.set(-side * (kerbX + 1.9), 0.028, centerZ - kerbZ + 0.45 + i * 2 * kerbZ / numStripes);
          stripes.push(stripe);
        }
      };
      if (situation.crosswalks.includes('entrance')) addAcrossMain(centerZ - kerbZ - 1.8);
      if (situation.crosswalks.includes('exit') && !tJunction) addAcrossMain(centerZ + kerbZ + 1.8);
      if (situation.crosswalks.includes('left')) addAcrossSide(-1);
      if (situation.crosswalks.includes('right')) addAcrossSide(1);
      const zebra = mergeStatic(stripes, markingMat); zebra.userData.crosswalk = true; seg.add(zebra);
    }

    // Rails are generated from actual tram trajectories below.

    // Traffic light
    let tlMesh = null;
    if (situation.trafficLights) {
      tlMesh = createTrafficLight(situation.trafficLights.state || 'green', situation.trafficLights.arrow);
      tlMesh.position.set(kerbX + 1.2, 0, stopLineZ);
      tlMesh.rotation.y = Math.PI;
      tlMesh.userData.editKey = 'light';
      seg.add(tlMesh);
    }

    const regConfig = situation.regulator || spec.regulator;
    if (regConfig) {
      const regMesh = createTrafficController(regConfig.pose || 'arms_down', regConfig.orientation || 'left_side');
      regMesh.position.set(0, 0, centerZ);
      seg.add(regMesh);
      seg.userData.regulator = regMesh;
      if (tlMesh) tlMesh.visible = false;
    }

    // Signs
    if (situation.signs && situation.signs.length > 0) {
      situation.signs.forEach((s, index) => {
        const sign = s.code === '8.13' ? createPriorityPlate(s.mainRoad,s.branches) : createRoadSign(s.code);
        const plate = s.code === '8.13';
        sign.position.set(s.x ?? (kerbX + 1.2), s.mountOnLight ? -1.05 : plate ? 1.5 : 0, s.z !== undefined ? centerZ + s.z : stopLineZ - 2.4 - (plate ? Math.max(0, index - 1) : index) * 2);
        if (s.mountOnLight) sign.children.filter(o => o.geometry?.type === 'CylinderGeometry').forEach(o => { o.visible = false; });
        sign.rotation.y = 0; // Facing oncoming player
        sign.userData.editKey = 'sign:' + index; sign.userData.signCode = s.code;
        seg.add(sign);
      });
    }

    if (oneWay) {
      // 3.1 "No entry" where the one-way street is left against its flow:
      // on the entering driver's right, facing the junction.
      const sx = oneWay === 'to_right' ? -1 : 1;
      const noEntry = createRoadSign('3.1');
      noEntry.userData.editKey = 'sign:noentry'; noEntry.userData.signCode = '3.1';
      noEntry.position.set(sx * (roadWidth / 2 + 9), 0, centerZ + (sx < 0 ? roadWidth / 2 + 1.0 : -(roadWidth / 2 + 1.0)));
      noEntry.rotation.y = sx < 0 ? -Math.PI / 2 : Math.PI / 2;
      seg.add(noEntry);
    }
    // Ticket trajectories (situation.trajectories: [{ label, points }] in
    // the factory frame, x = driver's right, z from the junction centre) are
    // drawn with the standard blue route chevrons (see the guide below); here
    // only their letters, on bright blue plates.
    const trajPaths = (situation.trajectories || []).map(t => curve(t.points.map(([x, z]) => new THREE.Vector3(x, 0, centerZ + z))));
    (situation.trajectories || []).forEach((t, n) => {
      if (!t.label) return;
      // Beside the arrow, on its outer side (away from the other routes),
      // still within the junction so it stays on screen.
      const path = trajPaths[n], u = 0.62;
      const at = path.getPointAt(u), tan = path.getTangentAt(u);
      const perp = new THREE.Vector3(-tan.z, 0, tan.x);
      const others = trajPaths.filter((_, k) => k !== n).map(p => p.getPointAt(u));
      const sideScore = sgn => others.reduce((sum, o) => sum + at.clone().addScaledVector(perp, sgn).distanceTo(o), 0);
      const sgn = others.length && sideScore(-1) > sideScore(1) ? -1 : 1;
      const label = createLetterToken(t.label);
      label.position.set(t.labelPosition?.[0] ?? (at.x + perp.x * sgn * 1.25), 0.8, t.labelPosition ? centerZ + t.labelPosition[1] : at.z + perp.z * sgn * 1.25); // child position: mirrored with the segment
      seg.add(label);
    });

    if (situation.stopPositions) {
      // Blue choice markers are explanatory annotations, never white 1.12 paint.
      for (const choice of situation.stopPositions) {
        const marker = addFlatPlane(seg, 3.5, 0.12, 1.8, centerZ + choice.z, 0.038,
          new THREE.MeshBasicMaterial({color: BRAND.accent}));
        marker.userData.questionEvidence = true;
        const label = createLetterToken(choice.label);
        label.position.set(-0.8, 0.8, centerZ + choice.z); seg.add(label);
      }
    }
    if(situation.noRight) {
      const cut=new THREE.Plane(new THREE.Vector3(1,0,0),4.2);
      for(const child of seg.children) {
        if(!child.isMesh || child.userData.editKey)continue;
        const c=child.material?.color?.getHex();
        if(child.userData.surface||child.userData.noRoad||child.userData.roadMarking||[BRAND.asphalt,BRAND.sidewalk,BRAND.asphaltMarking].includes(c)) {
          child.material=child.material.clone();child.material.clippingPlanes=[...(child.material.clippingPlanes||[]),cut];
        }
      }
      pavementRect(seg,3.2,52,5.8,centerZ);
    }
    if (situation.junctionLayout) buildAuthoredJunctionFabric(seg,centerZ,situation);
    if (situation.offsetTramRoad || situation.geometry==='motorway_parallel') buildSpecialMainFabric(seg,centerZ,situation);
    if (situation.geometry?.startsWith('courtyard_')) buildCourtyardQuestionFabric(seg, startZ, centerZ, situation);
    if (situation.yardAfter !== undefined) buildYardAfterQuestionFabric(seg, startZ, centerZ, situation);
    addLaneQuestionEvidence(seg, centerZ, situation);
    if (situation.mainMedian) {
      const width=situation.mainMedianWidth||.85,end=situation.mainMedianEnd??-9;
      const shape=new THREE.Shape(),half=width/2;
      shape.moveTo(-half,centerZ-26);shape.lineTo(half,centerZ-26);shape.lineTo(half,centerZ+end-half);
      shape.absarc(0,centerZ+end-half,half,0,Math.PI,false);shape.closePath();
      const geo=new THREE.ExtrudeGeometry(shape,{depth:.18,bevelEnabled:false,curveSegments:16});geo.rotateX(Math.PI/2);
      const median=new THREE.Mesh(geo,new THREE.MeshLambertMaterial({color:BRAND.sidewalk}));median.position.y=.18;median.userData.surface='sidewalk';median.userData.noRoad=p=>p.z>=centerZ-26&&p.z<=centerZ+end&&Math.abs(p.x)<half-.04&&(p.z<centerZ+end-half||Math.hypot(p.x,p.z-(centerZ+end-half))<half-.04);seg.add(median);
      const turf=new THREE.Mesh(new THREE.ShapeGeometry(shape),new THREE.MeshLambertMaterial({color:season().ground}));turf.rotation.x=Math.PI/2;turf.position.y=.186;turf.material.userData.seasonal='ground';seg.add(turf);
    }

    if(situation.residentialBackdrop) {
      const fence=createFence(44);fence.rotation.y=Math.PI/2;fence.position.set(0,0,centerZ+9);seg.add(fence);
      for(const x of [-22,-11,11,22]) {
        const home=createBuilding(7,4,7,0);home.position.set(x,0,centerZ+18);seg.add(home);
        const tree=createTree('round');tree.position.set(x+4,0,centerZ+11);seg.add(tree);
      }
    }
    // Place Actors
    const actorsInScene = [];
    if (situation.actorsConfig) {
      situation.actorsConfig.forEach(cfg => {
        const { actorMesh, halfLength, halfWidth } = createActorMesh(cfg);
        const approachOffset = Math.max(10, 5.5 + halfLength);
        // Reserve room for the whole vehicle, especially a bus/tram nose.
        if (cfg.position) {
          actorMesh.position.set(cfg.position[0], cfg.position[1] || 0, centerZ + cfg.position[2]);
          if (cfg.rotationY !== undefined) actorMesh.rotation.y = cfg.rotationY;
        } else if (cfg.side === 'cross_left' || cfg.side === 'left') {
          actorMesh.position.set(-approachOffset, 0, centerZ - 2.05);
          actorMesh.rotation.y = Math.PI / 2;
        } else if (cfg.side === 'cross_left_2') {
          actorMesh.position.set(-19, 0, centerZ - 2.05);
          actorMesh.rotation.y = Math.PI / 2;
        } else if (cfg.side === 'cross_right' || cfg.side === 'right') {
          actorMesh.position.set(approachOffset, 0, centerZ + 2.05);
          actorMesh.rotation.y = -Math.PI / 2;
        } else if (cfg.side === 'cross_right_2') {
          actorMesh.position.set(19, 0, centerZ + 2.05);
          actorMesh.rotation.y = -Math.PI / 2;
        } else if (cfg.side === 'opposite') {
          actorMesh.position.set(-1.8, 0, centerZ + Math.max(9, 5.5 + halfLength));
          actorMesh.rotation.y = Math.PI;
        } else if (cfg.side === 'opposite_right') {
          actorMesh.position.set(-1.8, 0, centerZ + 18);
          actorMesh.rotation.y = Math.PI;
        } else if (cfg.side === 'crosswalk_right') {
          actorMesh.position.set(kerbX + 1.9, 0.18, centerZ - kerbZ - 1.4);
        } else if (cfg.side === 'crosswalk_left') {
          actorMesh.position.set(-(kerbX + 1.9), 0.18, centerZ - kerbZ - 1.4);
        } else if (cfg.side === 'cross_right_edge') {
          actorMesh.position.set(3.35, 0, centerZ - 7.5);
          actorMesh.rotation.y = 0;
        } else {
          actorMesh.position.set(-6.8, 0, centerZ - 2.05);
          actorMesh.rotation.y = Math.PI / 2;
        }


        seg.add(actorMesh);
        if (cfg.hazard) actorMesh.userData.blinkerSide = 'hazard';
        actorsInScene.push({
          mesh: actorMesh,
          config: cfg,
          halfLength,
          halfWidth,
          initialPos: actorMesh.position.clone()
        });
      });
    }

    registerRoadSegment(seg);
    applySceneEdits(seg, situation.id, centerZ);
    actorsInScene.forEach(a => {
      a.initialPos = a.mesh.position.clone();
      a.viewBounds = new THREE.Box3().setFromObject(a.mesh);
    });
    state.roadSegments.push(seg);

    const intersectionData = {
      seg,
      startZ,
      centerZ,
      stopZ: situation.questionStop !== undefined ? centerZ + situation.questionStop : stopLineZ - 2.2,
      situation,
      actors: actorsInScene,
      trafficLight: tlMesh,
      // Lane the player turns into: the leftmost lane of the far carriageway
      // for a left turn (8.5), the rightmost lane for a right turn (8.6).
      leftLane: divided ? medianHalf + laneW / 2 : wide ? laneW / 2 : 1.8,
      rightLane: wide ? crossW / 2 - laneW / 2 : 1.8,
      halfW: wide ? halfW : null,
      halfM: wideMain ? halfM : null,
      kerbZ, kerbX,
    };
    state.intersections.push(intersectionData);
    // Visible participants already occupy the road, even before their question.
    // Register them now so traffic departing an earlier task can queue behind them.
    ensureTraffic(intersectionData);
    const action = spec.maneuver;
    const L = intersectionData.leftLane, R = intersectionData.rightLane;
    let guidePoints = action === 'right' ? [[-1.8, -R - 5.2], [-1.8, -R - 2.2], [-4, -R], [-16, -R]] :
      action === 'left' ? [[-1.8, -7], [-1.8, -1], [2, L], [16, L]] :
      action === 'uturn' ? [[-1.8, -7], [-2.5, 0], [0, 2.5], [2.5, 0], [1.8, -15]] : [[-1.8, -7], [-1.8, 16]];
    if (spec.paths?.[action]) guidePoints = spec.paths[action];
    // With ticket trajectories every one of them gets the chevrons (the
    // player's route is among them), so there is one arrow style on screen.
    let guidePaths = situation.trajectories?.length
      ? situation.trajectories.map(t => curve(t.points.map(([x, z]) => new THREE.Vector3(-x, 0.12, centerZ + z))))
      : [curve(guidePoints.map(([x, z]) => new THREE.Vector3(x, 0.12, centerZ + z)))];
    if (situation.yardAfter !== undefined || situation.geometry?.startsWith('courtyard_')) {
      // Show the turn into the entrance, not a route across the whole yard.
      guidePaths=guidePaths.map(path=>{
        const points=path.getSpacedPoints(Math.ceil(path.getLength()/.3));
        const end=points.findIndex(p=>Math.abs(p.x)>=10);
        return curve(end>1?points.slice(0,end+1):points);
      });
    }
    const guide = createRouteGuide(guidePaths);
    if (situation.trajectories?.length) guide.userData.questionEvidence = true;
    seg.add(guide); guide.visible = false;
    intersectionData.guide = guide;
    // Build every visible exit BEFORE a question or a camera turn. These
    // lightweight continuations are replaced seamlessly by the next full road.
    intersectionData.previews = {};
    const exitArms=situation.junctionLayout ? situation.junctionLayout.arms.map(a=>[a.exit,a.yaw,a.x,centerZ+a.z]) : [
      ['straight',0,0,startZ+intersectionLength],
      ['left',Math.PI/2,crossStreetLength/2,centerZ+(spec.exitOffsets?.left||0)],
      ['right',-Math.PI/2,-crossStreetLength/2,centerZ+(spec.exitOffsets?.right||0)],
    ];
    for (const [direction, yaw, x, z] of exitArms) {
      if (tJunction && direction === 'straight') continue;
      if (situation.noRight && direction === 'right') continue;
      if (situation.geometry==='motorway_parallel' && direction!=='straight')continue;
      if (situation.geometry?.startsWith('courtyard_') && situation.geometry !== 'courtyard_both' && direction !== 'straight' && direction !== situation.geometry.slice(10)) continue;
      // The one-way cross street continues past the junction as a one-way
      // road: turning with its flow leaves any lane usable, turning against
      // it is driving against the flow, never an ordinary "oncoming lane".
      const flowExit = oneWay === 'to_right' ? 'right' : 'left';
      const oneWayMode = oneWay && direction !== 'straight' ? (direction === flowExit ? 'with' : 'against') : null;
      const extension = dirtApproach && direction === 'right'
        ? buildDirtExit(200, (state.district + 1) % DISTRICTS, (crossStreetLength - roadWidth) / 2)
        : buildStraightSegment(0, 200, true, (state.district + 1) % DISTRICTS, oneWayMode, direction === 'straight' ? 0 : 30);
      extension.rotation.y = yaw;
      const yardSide=direction==='left'?1:-1;
      const yardExit=direction!=='straight' && (situation.yardAfter!==undefined
        ? spec.exitOffsets?.[direction]===situation.yardAfter && (situation.yardSides||[spec.maneuver==='left'?-1:1]).includes(-yardSide)
        : situation.geometry?.startsWith('courtyard_'));
      extension.position.set(yardExit?yardSide*33:x, 0, z);
      extension.userData.courtyardExit=!!yardExit;
      seg.add(extension);
      intersectionData.previews[direction] = extension;
    }
    if (incomingRoad) {
      // Reuse the actual approach, including its trees. A U-turn must not lay
      // another street and another junction over the one we just drove along.
      scene.updateMatrixWorld(true);
      const world = incomingRoad.matrixWorld.clone();
      seg.add(incomingRoad);
      incomingRoad.matrix.copy(world);
      world.decompose(incomingRoad.position, incomingRoad.quaternion, incomingRoad.scale);
      state.roadSegments = state.roadSegments.filter(s => s !== incomingRoad);
      intersectionData.previews.uturn = incomingRoad;
    }
    actorsInScene.filter(a => a.config.type === 'tram').forEach(a => {
      const motion = buildActorMotion(a, intersectionData);
      // The approach rails run along the tram's own heading (the path's first
      // tangent can already lean into the turn and skew them).
      const incoming = new THREE.Vector3(Math.sin(a.mesh.rotation.y), 0, Math.cos(a.mesh.rotation.y));
      const outgoing = motion.path.getTangentAt(1);
      const points = [a.initialPos.clone().addScaledVector(incoming, -70)];
      for (let i = 0; i <= 60; i++) points.push(motion.path.getPointAt(i / 60));
      // Actors continue beyond their authored curve until they have completely
      // left the camera. Rails must cover that same visual lifetime.
      points.push(motion.path.getPointAt(1).addScaledVector(outgoing, 320));
      const centerline = curve(points);
      [-0.7, 0.7].forEach(offset => {
        const rail = [];
        for (let i = 0; i <= 100; i++) {
          const t = i / 100, p = centerline.getPointAt(t), v = centerline.getTangentAt(t);
          p.add(new THREE.Vector3(-v.z, 0, v.x).multiplyScalar(offset));
          p.y = 0.055;
          rail.push(p);
        }
        const mesh = new THREE.Mesh(new THREE.TubeGeometry(curve(rail), 120, 0.035, 5, false),
          new THREE.MeshLambertMaterial({ color: 0x8E999C }));
        mesh.userData.tramRail = true;
        mesh.userData.railEnd = rail[rail.length - 1].clone();
        seg.add(mesh);
      });
    });

    refreshRoadBounds();
    return intersectionLength;
  }

  // Hand edits made in the game lab (tools/game_lab), per scenario id:
  // window.PDD_SCENE_EDITS[id] = { objects: [{ key, x, z, rotY, code, removed, add }] }.
  // x is world X (driver's right is negative), z is measured from the
  // scenario origin (junction centre / road-question stop point).
  const EDITABLE_DECOR = {
    tree: () => createTree(), pine: () => createTree('pine'), bush: () => createBush(),
    cone: () => createTrafficCone(), barrier: () => createRoadworksBarrier(2.4),
    lamp: () => createLampPost(), parked_car: () => createParkedCar(), kiosk: () => createKiosk(),
    fence: () => createFence(4), house: () => createBuilding(7, 4.5, 7, 1),
    triangle: () => createEmergencyTriangle(),
  };
  function createEditable(add) {
    if (add.type === 'sign') {
      const sign = createRoadSign(add.code);
      sign.userData.signCode = add.code;
      return sign;
    }
    const make = EDITABLE_DECOR[add.kind];
    if (!make) return null;
    const obj = make();
    obj.userData.decorKind = add.kind;
    return obj;
  }
  // Model workshop edits (colours, hidden parts, scale) for the engine's own
  // models; the player's cars get theirs inside vehicles.js.
  const modelEdited = (id, factory) => (...args) => window.PDD_VEHICLES.applyModelEdits(id, factory(...args));
  createNpcCar = modelEdited('car', createNpcCar);
  createBus = modelEdited('bus', createBus);
  createVan = modelEdited('van', createVan);
  createTruck = modelEdited('truck', createTruck);
  createTractor = modelEdited('tractor', createTractor);
  createSpecialCar = modelEdited('special', createSpecialCar);
  createMotorcycle = modelEdited('motorcycle', createMotorcycle);
  createTram = modelEdited('tram', createTram);
  createPedestrian = modelEdited('pedestrian', createPedestrian);
  createCyclist = modelEdited('cyclist', createCyclist);
  createTrafficCone = modelEdited('cone', createTrafficCone);
  createRoadworksBarrier = modelEdited('barrier', createRoadworksBarrier);
  createTrafficLight = modelEdited('traffic_light', createTrafficLight);
  createTree = modelEdited('tree', createTree);
  createLampPost = modelEdited('lamp', createLampPost);
  createKiosk = modelEdited('kiosk', createKiosk);
  createBuilding = modelEdited('building', createBuilding);
  function applySceneEdits(group, id, originZ) {
    // Stable keys for the rest of the scene's own objects (build order is
    // deterministic): trees, lamps, kiosks... Actors are never edited here.
    group.children.forEach((o, i) => {
      if (!o.userData.editKey && o.isGroup && !o.userData.actor) o.userData.editKey = 'obj:' + i;
    });
    const edits = (window.PDD_SCENE_EDITS || {})[id];
    if (!edits) return;
    const keyed = new Map();
    group.traverse(o => { if (o.userData.editKey) keyed.set(o.userData.editKey, o); });
    for (const e of edits.objects || []) {
      let obj = keyed.get(e.key);
      if (!obj && e.add) {
        obj = createEditable(e.add);
        if (!obj) continue;
        obj.userData.editKey = e.key;
        group.add(obj);
      }
      if (!obj) continue;
      if (e.code && obj.userData.signCode && e.code !== obj.userData.signCode) {
        const sign = createRoadSign(e.code);
        sign.position.copy(obj.position); sign.rotation.copy(obj.rotation); sign.scale.copy(obj.scale);
        sign.userData = { ...obj.userData, signCode: e.code };
        obj.parent.add(sign); obj.parent.remove(obj); obj = sign;
      }
      if (e.x !== undefined) obj.position.x = e.x;
      if (e.z !== undefined) obj.position.z = originZ + e.z;
      if (e.rotY !== undefined) obj.rotation.y = e.rotY;
      if (e.removed) obj.visible = false;
    }
  }

  // Road factories use X = driver's right. Convert once at their boundary to
  // Three's right-handed coordinates; never mirror meshes/textures themselves.
  function registerRoadSegment(seg) {
    // Paving joints, kerb sections and asphalt grain come from the shared road
    // textures (road-materials.js), continuous across segments.
    seg.children.forEach(child => {
      child.position.x *= -1;
      child.rotation.y *= -1;
    });
    seg.traverse(child => {
      if (child.isMesh && child.material && child.material.isMeshLambertMaterial) child.receiveShadow = true;
      if (!child.userData.actor && child.material?.color?.getHex() === BRAND.sidewalk) child.userData.surface = 'sidewalk';
      if (!child.userData.actor && child.material?.color?.getHex() === BRAND.asphalt && child.geometry?.type === 'PlaneGeometry') child.userData.surface = 'road';
    });
    seg.traverse(child => {
      if (child.userData.surface === 'sidewalk') { child.material.color.setHex(season().sidewalk); child.material.userData.seasonal = 'sidewalk'; }
    });
    // Its texture continues the road it was built from (a preview: the road
    // of its junction).
    window.PDD_ROADS.adopt(seg, state.exitRoad || currentCorridor);
    scene.add(seg);
  }

  function disposeSegment(seg) {
    if (state.roadEvent?.group === seg) finishRoadEvent(state.roadEvent.phase === 'manual');
    const removed = new Set(); seg.traverse(o => removed.add(o));
    state.ambient = state.ambient.filter(a => !removed.has(a.mesh));
    state.occluders = state.occluders.filter(o => !removed.has(o));
    if (seg.parent) seg.parent.remove(seg);
    const geometries = new Set(), materials = new Set(), textures = new Set();
    seg.traverse(o => o.userData.replacedMaterials?.forEach(m => materials.add(m)));
    seg.traverse(obj => {
      if (obj.geometry) geometries.add(obj.geometry);
      if (obj.material) (Array.isArray(obj.material) ? obj.material : [obj.material]).forEach(m => {
        materials.add(m);
        for (const key of ['map', 'bumpMap', 'normalMap', 'specularMap']) {
          const texture = m[key];
          if (texture && !texture.userData?.pddVehicleShared && !texture.userData?.pddRoadShared && ![...signTextureCache.values()].includes(texture)) textures.add(texture);
        }
      });
    });
    geometries.forEach(g => g.dispose());
    materials.forEach(m => m.dispose());
    textures.forEach(t => t.dispose());
    state.actors = state.actors.filter(a => a.segment !== seg);
  }

  function routeSpec(situation) {
    return situation.resolvedRoute || (window.PDD_SCENARIO_ROUTES || {})[situation.id] ||
      { maneuver: 'straight', yieldTo: [], reviewed: false };
  }

  function isRegulatorSituation(s) {
    const spec = routeSpec(s);
    return !!(s.regulator || spec.regulator || (spec.overrides && spec.overrides.regulator));
  }

  function nextSituation() {
    // Unreviewed geometry must not silently teach an incorrect scene.
    const pool = SITUATIONS.filter(s => routeSpec(s).reviewed === true);
    if (!pool.length) throw new Error('No validated driving scenarios loaded');

    if (situationBag.length) {
      const selected = situationBag.pop();
      lastSituationId = selected.id;
      return selected;
    }

    const regPool = pool.filter(isRegulatorSituation);
    const normalPool = pool.filter(s => !isRegulatorSituation(s));

    // One junction with a traffic controller per run, somewhere between the
    // 3rd and the 8th (a run of 20 questions passes about ten junctions).
    state.junctionsDrawn = (state.junctionsDrawn || 0) + 1;
    if (state.regulatorAt === undefined) state.regulatorAt = 3 + Math.floor(Math.random() * 6);
    const wantRegulator = Boolean(state.forceRegulator) || state.junctionsDrawn === state.regulatorAt;

    if (wantRegulator && regPool.length) {
      const idx = Math.floor(Math.random() * regPool.length);
      const selected = regPool[idx];
      lastSituationId = selected.id;
      return selected;
    }

    const availablePool = normalPool.length ? normalPool : pool;
    situationBag = availablePool.slice();
    for (let i = situationBag.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [situationBag[i], situationBag[j]] = [situationBag[j], situationBag[i]];
    }
    if (situationBag.length > 1 && situationBag[situationBag.length - 1].id === lastSituationId) {
      [situationBag[0], situationBag[situationBag.length - 1]] =
        [situationBag[situationBag.length - 1], situationBag[0]];
    }
    const selected = situationBag.pop();
    lastSituationId = selected.id;
    return selected;
  }

  function buildInitialTrack() {
    buildStraightSegment(-150, 200);
    const incoming = state.roadSegments[state.roadSegments.length - 1];
    currentCorridor = incoming;
    buildIntersectionSegment(50, nextSituation(), incoming);
    nextSegmentZ = 102;
    resolveSceneryOverlaps();
  }

  // Streets are built independently, and at a junction's outer corners the
  // houses of the road going on and of the cross street claim the same plot.
  // A newly built house that overlaps one already standing is left out, and
  // so is any tree, lamp, fence or bench that would stand inside a house.
  function resolveSceneryOverlaps() {
    scene.updateMatrixWorld(true);
    const overlap = (a, b, margin) => Math.min(a.max.x, b.max.x) - Math.max(a.min.x, b.min.x) > margin &&
      Math.min(a.max.z, b.max.z) - Math.max(a.min.z, b.min.z) > margin;
    const houses = [];
    for (const building of state.occluders) {
      if (!building.parent || !building.visible) continue;
      const box = new THREE.Box3().setFromObject(building);
      if (box.isEmpty()) continue;
      if (houses.some(h => overlap(h.box, box, 0.3))) { building.visible = false; continue; }
      houses.push({ building, box });
    }
    const houseSet = new Set(houses.map(h => h.building));
    state.roadSegments.forEach(seg => seg.traverse(o => {
      if (!o.userData.sceneryObject || houseSet.has(o) || !o.visible) return;
      if (state.occluders.includes(o)) return;
      const box = new THREE.Box3().setFromObject(o);
      if (box.isEmpty()) return;
      const cx = (box.min.x + box.max.x) / 2, cz = (box.min.z + box.max.z) / 2;
      if (houses.some(h => cx > h.box.min.x + 0.2 && cx < h.box.max.x - 0.2 && cz > h.box.min.z + 0.2 && cz < h.box.max.z - 0.2)) o.visible = false;
    }));
  }

  function checkAndSpawnNext() {
    if (!state.isAtSituation && !state.resolution && maybeReverseWorld()) return;
    if (state.isResolvingSituation || state.intersections.length) return;
    if (playerCarGroup.position.z + 110 > nextSegmentZ) {
      situationIndex++;
      buildIntersectionSegment(nextSegmentZ, nextSituation(), state.exitRoad);
      state.exitRoad = null;
      resolveSceneryOverlaps();
    }
    trimSegments();
  }

  // Both the removed geometry and its GPU resources have a bounded lifetime,
  // whatever pushed the newest segment (junction, exit road or road event).
  function trimSegments() {
    if (state.roadSegments.length <= 8) return;
    while (state.roadSegments.length > 8) disposeSegment(state.roadSegments.shift());
    refreshRoadBounds();
  }

  function corridorWorldEnds() {
    if (!currentCorridor?.userData.roadEnds) return [];
    currentCorridor.updateWorldMatrix(true, false);
    return currentCorridor.userData.roadEnds.map(p => p.clone().applyMatrix4(currentCorridor.matrixWorld));
  }

  function maybeReverseWorld(force = false) {
    if (!currentCorridor || state.isAtSituation || state.resolution || Math.cos(playerCarGroup.rotation.y) > -0.55) return false;
    state.laneChangeX = null; state.autoPath = null; state.trail = [];
    const forward = new THREE.Vector3(Math.sin(playerCarGroup.rotation.y), 0, Math.cos(playerCarGroup.rotation.y));
    const distanceToEnd = Math.max(...corridorWorldEnds().map(p => p.clone().sub(playerCarGroup.position).dot(forward)));
    if (!force && distanceToEnd > 105) return false;

    // Passive coordinate rebase around the road centre beside the player.
    // Applying the same transform to camera and world keeps the rendered frame
    // unchanged, while the player's travel direction becomes local +Z again.
    const pivot = new THREE.Vector3(0, 0, playerCarGroup.position.z);
    const transform = new THREE.Matrix4().makeTranslation(pivot.x, 0, pivot.z)
      .multiply(new THREE.Matrix4().makeRotationY(Math.PI))
      .multiply(new THREE.Matrix4().makeTranslation(-pivot.x, 0, -pivot.z));
    state.roadSegments.forEach(seg => seg.applyMatrix4(transform));
    window.PDD_ROADS.rebase(transform);
    const planes = new Set();
    state.roadSegments.forEach(seg => seg.traverse(o => {
      const materials = Array.isArray(o.material) ? o.material : [o.material];
      materials.forEach(m => (m?.clippingPlanes || []).forEach(p => planes.add(p)));
    }));
    planes.forEach(p => p.applyMatrix4(transform));
    camera.position.applyMatrix4(transform); cameraLook.applyMatrix4(transform);
    playerCarGroup.applyMatrix4(transform);
    state.lastSafePosition.applyMatrix4(transform);
    cameraHeading += Math.PI;

    scene.updateMatrixWorld(true);
    const corridorWorld = currentCorridor.matrixWorld.clone();
    if (currentCorridor.parent) currentCorridor.parent.remove(currentCorridor);
    scene.add(currentCorridor);
    corridorWorld.decompose(currentCorridor.position, currentCorridor.quaternion, currentCorridor.scale);
    cancelRoadEvent();
    // Scenes along this very road (a car in a driveway, a bus at its stop,
    // road works) stay where they are and keep moving: only the junctions
    // at its ends are rebuilt. Nothing the player is looking at vanishes.
    const kept = new Set(state.roadSegments.filter(seg => seg === currentCorridor || seg.userData.roadEvent));
    const retired = state.roadSegments.filter(seg => !kept.has(seg));
    retired.forEach(disposeSegment);
    state.roadSegments = [...kept];
    state.intersections = [];
    state.activeIntersection = null;
    const inKept = a => { let o = a.mesh; while (o && !kept.has(o)) o = o.parent; return !!o; };
    state.actors = state.actors.filter(a => !a.done && inKept(a));
    // Their question/event is over: anyone waiting for the player moves on.
    state.actors.forEach(a => { a.waitsForPlayer = false; if (a.stopFor === Infinity) a.stopFor = 1.2; });
    state.exitRoad = currentCorridor;
    state.sideJunction = null;
    clearOncoming();
    state.speedLimitKmH = null;
    state.speedingTime = 0;
    state.speedingPenalized = false;

    const ends = corridorWorldEnds();
    const startZ = Math.max(...ends.map(p => p.z));
    state.district = (state.district + 1) % DISTRICTS;
    buildIntersectionSegment(startZ, nextSituation(), currentCorridor);
    nextSegmentZ = startZ + 52;
    refreshRoadBounds();
    return true;
  }

  function curve(points) {
    return new THREE.CatmullRomCurve3(points, false, 'centripetal');
  }

  function buildActorMotion(actor, intersection) {
    const p = actor.initialPos.clone();
    const cfg = actor.config;
    const z = intersection.centerZ;
    let points, clearDistance;
    if (cfg.route) {
      // An authored route ([x, z from the centre], world axes). The actor has
      // passed once it is out of the junction box.
      points = [p, ...cfg.route.map(([x, dz]) => new THREE.Vector3(x, cfg.pathHeight ?? 0, z + dz))];
      const box = (intersection.kerbZ || 4.2) + 1.5;
      const raw = curve(points), n = Math.ceil(raw.getLength());
      let out = raw.getLength();
      for (let i = 1; i <= n; i++) {
        const q = raw.getPointAt(i / n);
        if (i / n > 0.2 && (Math.abs(q.x) > box || Math.abs(q.z - z) > box)) { out = raw.getLength() * i / n; break; }
      }
      clearDistance = out + actor.halfLength + 1;
    } else if (cfg.type === 'pedestrian') {
      // Cross the destination road, then continue along the pavement. The
      // crossing may be unmarked, as in the source ticket.
      const x = p.x;
      const k = intersection.kerbZ || 4.2;
      points = [p, new THREE.Vector3(x, 0.03, z - k + 0.4),
        new THREE.Vector3(x, 0.03, z + k - 0.4),
        new THREE.Vector3(x, 0.18, z + k + 1.6),
        new THREE.Vector3(x * 1.8, 0.18, z + k + 1.9),
        new THREE.Vector3(Math.sign(x) * 48, 0.18, z + k + 1.9)];
      clearDistance = 12.5;
    } else {
      const yaw = actor.mesh.rotation.y;
      const forward = new THREE.Vector3(Math.sin(yaw), 0, Math.cos(yaw));
      if (intersection.situation.geometry === 'roundabout' && cfg.side !== 'ring' && !cfg.roundabout && cfg.type !== 'tram') {
        // Traffic entering a roundabout drives round the ring counter-
        // clockwise to its exit — never straight across the island. The
        // player's own ring paths, turned to this actor's approach.
        const T = {
          right: [[-1.8, -18], [-3.5, -14], [-7.5, -10], [-12, -4], [-18, -1.8], [-40, -1.8]],
          straight: [[-1.8, -18], [-4.0, -14], [-9.5, -6], [-10.5, 0], [-8.5, 8], [-4.0, 14], [-1.8, 18], [-1.8, 40]],
          left: [[-1.8, -18], [-4.0, -14], [-9.5, -6], [-10.5, 0], [-8.5, 8], [0, 11.5], [8.5, 8], [14, 4], [18, 1.8], [40, 1.8]],
        }[cfg.targetAction === 'turn_right' ? 'right' : cfg.targetAction === 'turn_left' || cfg.targetAction === 'uturn' ? 'left' : 'straight'];
        const c = Math.cos(yaw), sn = Math.sin(yaw);
        const toWorld = ([lx, lz]) => new THREE.Vector3(lx * c + lz * sn, 0, z - lx * sn + lz * c);
        const route = T.map(toWorld).filter(q => q.clone().sub(p).dot(forward) > 0.5 || q.distanceTo(new THREE.Vector3(0, 0, z)) < 16);
        points = [p, ...route];
        clearDistance = 26;
      } else if (cfg.side === 'ring' || cfg.roundabout) {
        // Round the ring counter-clockwise and leave by the arm nearest to
        // three quarters of a turn, along that arm's exit lane. (Leaving on
        // the tangent drove straight across an arm and its verge, and the
        // vehicle counted as passed while it was still circling towards the
        // player's entry.)
        const ringRadius = cfg.ringRadius || 12.0;
        const startAngle = Math.atan2(p.x, p.z - z);
        const exitArm = Math.round((startAngle + Math.PI * 1.5) / (Math.PI / 2)) * (Math.PI / 2);
        const arcEnd = exitArm - 0.35;
        const onRing = a => new THREE.Vector3(ringRadius * Math.sin(a), 0, z + ringRadius * Math.cos(a));
        const arcPoints = [p];
        for (let a = startAngle + 0.35; a < arcEnd - 0.1; a += 0.35) arcPoints.push(onRing(a));
        arcPoints.push(onRing(arcEnd));
        const out = new THREE.Vector3(Math.sin(exitArm), 0, Math.cos(exitArm));
        const right = new THREE.Vector3(-Math.cos(exitArm), 0, Math.sin(exitArm));
        const lane = r => new THREE.Vector3(0, 0, z).addScaledVector(out, r).addScaledVector(right, 1.8);
        points = [...arcPoints, lane(16.5), lane(24), lane(60)];
        clearDistance = ringRadius * (arcEnd - startAngle) + 9 + actor.halfLength;
      } else if (cfg.targetAction === 'uturn') {
        const side = new THREE.Vector3(Math.cos(yaw), 0, -Math.sin(yaw));
        const entry = p.clone().addScaledVector(forward, 5);
        const exit = entry.clone().addScaledVector(side, 3.6);
        points = [p, entry, entry.clone().addScaledVector(forward, 2).addScaledVector(side, 1.8),
          exit, exit.clone().addScaledVector(forward, -50)];
        clearDistance = 20;
      } else if (cfg.targetAction === 'turn_left' || cfg.targetAction === 'turn_right') {
        const turn = cfg.targetAction === 'turn_left' ? Math.PI / 2 : -Math.PI / 2;
        const outgoing = new THREE.Vector3(Math.sin(yaw + turn), 0, Math.cos(yaw + turn));
        const center = new THREE.Vector3(0, 0, z);
        // Keep the actual approach lane (including offset tram tracks) until
        // the junction. Snapping all approaches to 1.8m made turning trams
        // sweep into the adjacent waiting car before reaching the crossing.
        const lateral = p.clone().sub(center);
        lateral.addScaledVector(forward, -lateral.dot(forward));
        const approach = center.clone().addScaledVector(forward, -6).add(lateral);
        const entry = center.clone().addScaledVector(forward, -2).add(lateral);
        // Stay on the right-hand half of the outgoing carriageway.
        const right = new THREE.Vector3(-outgoing.z, 0, outgoing.x);
        const exit = center.clone().addScaledVector(outgoing, 6).addScaledVector(right, 1.8);
        points = [p, approach, entry, exit, exit.clone().addScaledVector(outgoing, 10), exit.clone().addScaledVector(outgoing, 45)];
        clearDistance = p.distanceTo(entry) + entry.distanceTo(exit) + actor.halfLength + 3;
        if (cfg.type === 'tram') {
          // Rails turn on a true circular arc tangent to both tracks, never
          // a kink: the corner K where the two track lines meet is rounded
          // with the largest radius the junction allows.
          const exitLine = center.clone().addScaledVector(right, 1.8);
          const K = center.clone().add(lateral).addScaledVector(forward, exitLine.clone().sub(center).dot(forward));
          const R = Math.max(3, Math.min(9, K.clone().sub(p).dot(forward) - 0.5));
          const A = K.clone().addScaledVector(forward, -R), B = K.clone().addScaledVector(outgoing, R);
          const O = A.clone().addScaledVector(outgoing, R);
          const arc = [];
          for (let i = 0; i <= 12; i++) {
            const t = i / 12 * Math.PI / 2;
            arc.push(O.clone().addScaledVector(outgoing, -R * Math.cos(t)).addScaledVector(forward, R * Math.sin(t)));
          }
          // The arc starts at A; no extra point that could fold the rails back.
          const lead = A.clone().sub(p).dot(forward);
          points = [p, ...arc.filter(q => q.clone().sub(p).dot(forward) > 0.5 || q.clone().sub(p).dot(outgoing) > 0.5),
            B.clone().addScaledVector(outgoing, 10), B.clone().addScaledVector(outgoing, 45)];
          clearDistance = p.distanceTo(A) + R * Math.PI / 2 + actor.halfLength + 3;
        }
      } else {
        points = [p, p.clone().addScaledVector(forward, 16), p.clone().addScaledVector(forward, 65)];
        clearDistance = cfg.type === 'cyclist' ? 15 :
          (Math.abs(p.x) > 5 ? Math.abs(p.x) : Math.abs(p.z - z)) + 5.5 + actor.halfLength;
      }
    }
    if ((intersection.halfW || intersection.halfM) && cfg.type !== 'pedestrian' && !cfg.exactRoute) {
      // On a tapering wide street every lane closes in towards the centre
      // with the kerbs, smoothly (the rails follow the same path).
      const hw = intersection.halfW, hm = intersection.halfM;
      const raw = curve(points), n = Math.ceil(raw.getLength() / 2);
      points = Array.from({ length: n + 1 }, (_, i) => {
        const q = raw.getPointAt(i / n);
        if (hw && Math.abs(q.x) > 8) q.z = z + (q.z - z) * hw(q.x) / hw(0);
        if (hm && Math.abs(q.z - z) > 12 && Math.abs(q.x) < 8) q.x = q.x * hm(q.z) / hm(z);
        return q;
      });
    }
    const path = curve(points);
    // Turning traffic signals its manoeuvre until the turn is complete.
    const signalPlan = cfg.targetAction === 'turn_right' ? [{ from: 0, to: clearDistance, side: 'right' }] :
      (cfg.targetAction === 'turn_left' || cfg.targetAction === 'uturn') ? [{ from: 0, to: clearDistance, side: 'left' }] : null;
    return { ...actor, segment: intersection.seg, path, length: path.getLength(),
      distance: 0, speed: 0, maxSpeed: cfg.type === 'pedestrian' ? 3.6 : cfg.type === 'cyclist' ? 7 : cfg.type === 'cart' ? 5 : 12,
      clearDistance, active: false, waitsForPlayer: true, cleared: false, done: false, gait: 0, signalPlan,
      stopAtDistance: cfg.stationary ? 0 : cfg.stopAtDistance, stopFor: cfg.stationary ? Infinity : cfg.stopFor, holdFor: cfg.holdFor, home: intersection };
  }

  // A staged participant (config.holdFor) has already rolled out onto the
  // junction and waits at its stop point until the player has left the
  // junction ('player') and the listed participants have passed (8_14).
  function holdPending(a) {
    return a.holdFor.some(id => id === 'player' ? state.intersections.includes(a.home) :
      (a.home.motions || []).some(b => b.config.id === id && !b.cleared));
  }

  function ensureTraffic(intersection) {
    if (!intersection.motions) {
      intersection.motions = intersection.actors.map(a => buildActorMotion(a, intersection));
      state.actors.push(...intersection.motions);
    }
    return intersection.motions;
  }

  function releaseTraffic(situationId) {
    if (state.roadEvent?.phase === 'question' && state.roadEvent.situation.id === situationId) {
      releaseRoadActors(state.roadEvent);
      return;
    }
    const intersection = state.activeIntersection;
    if (!intersection || intersection.situation.id !== situationId || intersection.trafficReleased) return;
    intersection.trafficReleased = true;
    if (intersection.trafficLight && !intersection.trafficLight.userData.arrow &&
        intersection.situation.trafficLights.state !== 'flashing_yellow') {
      intersection.trafficLight.setLightState('green');
    }
    const motions = ensureTraffic(intersection);
    const priority = routeSpec(intersection.situation).yieldTo;
    const ordered = [...motions.filter(a => priority.includes(a.config.id)), ...motions.filter(a => !priority.includes(a.config.id))];
    ordered.forEach((a, i) => {
      a.waitsForPlayer = false;
      a.dependencies = ordered.slice(0, i).filter(b => pathsConflict(a, b));
    });
  }

  function resolveSituationAnimation(isCorrect, situationId) {
    if (state.roadEvent?.phase === 'question' && state.roadEvent.situation.id === situationId) {
      if (!state.paused && state.isAtSituation) startRoadManual();
      return;
    }
    const intersection = state.activeIntersection;
    if (state.paused || state.isResolvingSituation || !state.isAtSituation || !intersection) return;
    if (situationId && situationId !== intersection.situation.id) return;
    resetQuestionCamera();
    state.isResolvingSituation = true;
    state.isAccelerating = false;
    state.speed = 0;
    const spec = routeSpec(intersection.situation);
    const motions = ensureTraffic(intersection);
    hideBadges(motions);
    const yielding = spec.yieldTo.map(id => motions.find(a => a.config.id === id)).filter(Boolean);
    state.resolution = { intersection, spec, motions, yielding, phase: 'manual', elapsed: 0,
      entry: playerCarGroup.position.clone(), entryYaw: playerCarGroup.rotation.y, faults: new Set(), recovery: 0 };
    if (spec.pathRules) state.resolution.pathAudit = buildManeuverAudit(state.resolution);
    state.steering = 0; state.laneChangeX = null; state.autoPath = null;
    startPlayerManeuver();
    const r = state.resolution;
    const intended = { path: r.path, length: r.length, clearDistance: r.length, halfWidth: 0.9, halfLength: 2 };
    const ordered = [...yielding, ...motions.filter(a => !yielding.includes(a))];
    ordered.forEach((a, i) => {
      a.dependencies = ordered.slice(0, i).filter(b => pathsConflict(a, b));
      a.waitsForPlayer = !intersection.trafficReleased && !yielding.includes(a) && pathsConflict(a, intended);
    });
  }

  function startPlayerManeuver() {
    const r = state.resolution;
    if (!r) return;
    const { points, exitYaw } = maneuverPoints(r, r.spec.maneuver, playerCarGroup.position.clone());
    const action = r.spec.maneuver;
    r.phase = 'manual';
    r.path = curve(points);
    r.length = r.path.getLength();
    r.distance = 0;
    r.exitYaw = exitYaw;
    if (state.simpleSteering) {
      // The player chooses the exit with the arrows; straight on by default
      // (a T-junction waits at the turn until a side is chosen).
      const previews = r.intersection.previews || {};
      r.simpleOpen = true;
      // The choice closes where the manoeuvre begins: at the turn, or at
      // the entry to the ring.
      r.simpleGate = r.intersection.situation.geometry === 'roundabout' ? r.intersection.centerZ - 17
        : r.intersection.centerZ - (r.intersection.rightLane || 1.8) - 3;
      r.simpleChoice = previews.straight ? 'straight' : null;
      r.simpleDeviated = false;
      applyJunctionChoice(r);
    } else if (action !== 'straight') triggerBlinker(action === 'right' ? 'right' : 'left');
    if (r.intersection.trafficLight && !r.intersection.trafficLight.userData.arrow &&
        r.intersection.situation.trafficLights.state !== 'flashing_yellow' && !r.intersection.situation.redWait) {
      r.intersection.trafficLight.setLightState('green');
    }
  }

  function maneuverPoints(r, action, start) {
    const z = r.intersection.centerZ;
    let points, exitYaw = 0;
    const custom = r.spec.paths?.[action];
    if (custom) {
      // An authored route for this scene ([x, z from the centre], world
      // axes): e.g. a left turn wide enough to pass an opposing left-turner.
      exitYaw = r.intersection.situation.junctionLayout?.arms.find(a=>a.exit===action)?.yaw ?? ({ left: Math.PI / 2, right: -Math.PI / 2, uturn: Math.PI }[action] || 0);
      points = [start, ...custom.map(([x, dz]) => new THREE.Vector3(x, 0, z + dz))];
    } else if (r.intersection.situation.geometry === 'roundabout') {
      if (action === 'right') {
        exitYaw = -Math.PI / 2;
        points = [start, new THREE.Vector3(-1.8, 0, z - 18), new THREE.Vector3(-3.5, 0, z - 14),
          new THREE.Vector3(-7.5, 0, z - 10), new THREE.Vector3(-12, 0, z - 4), new THREE.Vector3(-18, 0, z - 1.8), new THREE.Vector3(-24, 0, z - 1.8)];
      } else if (action === 'straight') {
        exitYaw = 0;
        points = [start, new THREE.Vector3(-1.8, 0, z - 18), new THREE.Vector3(-4.0, 0, z - 14),
          new THREE.Vector3(-9.5, 0, z - 6), new THREE.Vector3(-10.5, 0, z), new THREE.Vector3(-8.5, 0, z + 8),
          new THREE.Vector3(-4.0, 0, z + 14), new THREE.Vector3(-1.8, 0, z + 18), new THREE.Vector3(-1.8, 0, z + 26)];
      } else {
        exitYaw = Math.PI / 2;
        points = [start, new THREE.Vector3(-1.8, 0, z - 18), new THREE.Vector3(-4.0, 0, z - 14),
          new THREE.Vector3(-9.5, 0, z - 6), new THREE.Vector3(-10.5, 0, z), new THREE.Vector3(-8.5, 0, z + 8),
          new THREE.Vector3(0, 0, z + 11.5), new THREE.Vector3(8.5, 0, z + 8), new THREE.Vector3(14, 0, z + 4),
          new THREE.Vector3(18, 0, z + 1.8), new THREE.Vector3(24, 0, z + 1.8)];
      }
    } else if (action === 'right') {
      exitYaw = -Math.PI / 2;
      const R = r.intersection.rightLane || 1.8;
      points = [start, new THREE.Vector3(-1.8, 0, z - R - 3),
        new THREE.Vector3(-4.8, 0, z - R), new THREE.Vector3(-22, 0, z - R)];
      const hw = r.intersection.halfW;
      // On a wide street the lane closes in with the taper to the exit road.
      if (hw) points.splice(3, 1, new THREE.Vector3(-14, 0, z - R), new THREE.Vector3(-26, 0, z - R * hw(26) / hw(0)), new THREE.Vector3(-36, 0, z - 1.8));
    } else if (action === 'left') {
      exitYaw = Math.PI / 2;
      const L = r.intersection.leftLane || 1.8;
      // From the lane the car is in (the left one on a wider road).
      points = [start, new THREE.Vector3(THREE.MathUtils.clamp(start.x, -1.8, 1.8), 0, z - 1.5),
        new THREE.Vector3(1.5, 0, z + L), new THREE.Vector3(22, 0, z + L)];
      const hw = r.intersection.halfW;
      if (hw) points.splice(3, 1, new THREE.Vector3(14, 0, z + L), new THREE.Vector3(26, 0, z + L * hw(26) / hw(0)), new THREE.Vector3(36, 0, z + 1.8));
    } else if (action === 'uturn') {
      exitYaw = Math.PI;
      // A round loop in the open middle of the junction (radius 2.6 m), no
      // swing out to the right kerb of the approach first (the car's corner
      // caught it). Sampled densely: a few loose points made a kink where
      // the car turned 80° within a metre.
      const R = 2.6, zc = z + 0.8, arc = [];
      for (let a = 180; a >= 0; a -= 15) arc.push(new THREE.Vector3(R * Math.cos(a * Math.PI / 180), 0, zc + R * Math.sin(a * Math.PI / 180)));
      points = [start, new THREE.Vector3(-1.8, 0, z - 7), new THREE.Vector3(-R, 0, zc - 2.5), ...arc,
        new THREE.Vector3(R, 0, zc - 2.5), new THREE.Vector3(1.8, 0, z - 7), new THREE.Vector3(1.8, 0, z - 22)];
    } else {
      points = [start, new THREE.Vector3(-1.8, 0, z), new THREE.Vector3(-1.8, 0, z + 16)];
    }
    return { points, exitYaw };
  }

  function followingSpeed(actor, traffic, dt) {
    if (actor.config.type === 'pedestrian') return actor.maxSpeed;
    const box = traffic.get(actor).box;
    const forward = new THREE.Vector3(Math.sin(box.yaw), 0, Math.cos(box.yaw));
    const right = new THREE.Vector3(forward.z, 0, -forward.x);
    let limit = actor.maxSpeed;
    for (const [other, entry] of traffic) {
      if (other === actor || other.config.type === 'pedestrian') continue;
      const leader = entry.box, alignment = Math.cos(leader.yaw - box.yaw);
      if (alignment < 0.4) continue; // Crossing traffic uses the conflict rules.
      const delta = leader.p.clone().sub(box.p), ahead = delta.dot(forward);
      if (ahead <= 0) continue;
      const across = Math.abs(Math.sin(leader.yaw - box.yaw));
      const width = alignment * leader.halfWidth + across * leader.halfLength;
      if (Math.abs(delta.dot(right)) >= box.halfWidth + width + 0.15) continue;
      const gap = ahead - box.halfLength - alignment * leader.halfLength - across * leader.halfWidth;
      const room = Math.max(0, gap - 1.4);
      const speed = entry.speed * alignment;
      // Stopping distance plus 0.8s headway; stopped queues retain a 1.4m gap.
      // Also cap this frame's travel, including long frames and a stopped leader.
      const braking = 8, headway = 0.8;
      const safe = Math.sqrt((braking * headway) ** 2 + speed * speed + 2 * braking * room) - braking * headway;
      limit = Math.min(limit, safe, room / Math.max(dt, 0.001));
    }
    return Math.max(0, limit);
  }

  // Through traffic (road-event vehicles, traffic leaving an earlier task)
  // follows the road network: at a T-junction ahead there is no straight on,
  // so it turns right instead of driving over the far pavement.
  function rerouteAtTJunctions() {
    // T-junction: no straight on — turn right. Roundabout: go round the ring
    // (counter-clockwise, keeping right) and leave straight ahead.
    const tees = state.intersections.filter(it => ['t_no_straight', 'roundabout'].includes(it.situation.geometry));
    if (!tees.length) return;
    for (const a of state.actors) {
      if (a.done || a.fall || a.crashed || a.rerouted || ['pedestrian', 'tram'].includes(a.config.type)) continue;
      const tee = tees.find(it => !it.actors.some(x => x.mesh === a.mesh));
      if (!tee) continue;
      const pos = a.mesh.getWorldPosition(new THREE.Vector3());
      const c = tee.centerZ, t = Math.min(1, a.distance / a.length);
      const tangent = a.path.getTangentAt(t).transformDirection(a.mesh.parent.matrixWorld);
      if (tangent.z < 0.8 || pos.z > c - 7 || pos.z < c - 40 || Math.abs(pos.x) > 4.3) continue;
      const end = a.path.getPointAt(1).applyMatrix4(a.mesh.parent.matrixWorld);
      if (end.z < c || Math.abs(end.x) > 5) continue; // only paths that go straight on through it
      const x = pos.x, lane = c - 1.8, V = (px, pz) => new THREE.Vector3(px, 0, pz);
      const roundabout = tee.situation.geometry === 'roundabout';
      if (roundabout && pos.z > c - 19) continue; // too late to join the ring properly
      const world = roundabout
        ? [pos, V(-1.8, c - 18), V(-4.0, c - 14), V(-9.5, c - 6), V(-10.5, c), V(-8.5, c + 8), V(-4.0, c + 14),
          V(-1.8, c + 18), V(-1.8, c + 40), V(-1.8, c + 320)]
        : [pos, V(x, c - 6), V(x - 1.2, c - 3.4), V(x - 4.2, lane), V(-40, lane), V(-320, lane)];
      a.path = curve(world.map(p => a.mesh.parent.worldToLocal(p.clone())));
      a.length = a.path.getLength(); a.distance = 0; a.rerouted = true;
      a.holdSpeedUntil = undefined; a.stopAtDistance = undefined;
      // Signal right for the turn / before leaving the ring (8.1, 8.6).
      a.signalPlan = roundabout ? [{ from: a.length - 300, to: a.length - 290, side: 'right' }] : [{ from: 0, to: 18, side: 'right' }];
      a.clearDistance = Infinity;
    }
  }

  function spinActorWheels(mesh, distance) {
    mesh.userData.wheels?.forEach(w => w.rotateX(distance / 0.36));
    // Commercial rims are separate editable parts, rather than tyre children.
    mesh.userData.rims?.forEach(w => w.rotateX(distance / 0.36));
  }

  function updateActors(dt) {
    const emergency = state.roadEvent;
    if (emergency?.kind === 'emergency_lane' && emergency.phase === 'approach') {
      const car = emergency.police;
      // Catch the player from behind, but reserve room for the question and
      // braking. Never pass them before they have been asked to give way.
      const room = playerCarGroup.position.z - car.mesh.position.z - 10;
      car.maxSpeed = Math.max(0, Math.min(24, state.speed + 5, room / Math.max(dt, 0.001)));
    }
    rerouteAtTJunctions();
    state.busBays = state.busBays.filter(b => b.mesh.parent);
    // Walkers meeting on the same pavement lane step to the other lane and
    // pass each other instead of walking through one another.
    for (let i = 0; i < state.ambient.length; i++) {
      const a = state.ambient[i];
      if (a.targetLane !== a.lane && Math.abs(a.mesh.position.z - a.meetZ) > 4) a.targetLane = a.lane;
      if (a.kind === 'cat') continue;
      for (let j = i + 1; j < state.ambient.length; j++) {
        const b = state.ambient[j];
        if (b.kind === 'cat' || b.seg !== a.seg || b.side !== a.side || a.targetLane !== b.targetLane) continue;
        if (Math.abs(a.mesh.position.z - b.mesh.position.z) < 2.4) { a.targetLane = 1 - a.targetLane; a.meetZ = a.mesh.position.z; }
      }
    }
    state.ambient.forEach(a => {
      a.time += dt;
      if (a.kind === 'cat') {
        // Short strolls with long pauses, a flick of the tail while sitting.
        const cycle = a.time * 0.09 + a.phase, moving = Math.abs(Math.cos(cycle)) > 0.55;
        if (moving) a.mesh.position.z = a.center + Math.sin(cycle) * 1.6;
        a.mesh.rotation.y = Math.cos(cycle) >= 0 ? 0 : Math.PI;
        a.mesh.userData.legs.forEach((leg, i) => { leg.rotation.x = moving ? Math.sin(a.time * 9 + i * Math.PI / 2) * 0.5 : 0; });
        a.mesh.userData.tail.rotation.z = Math.sin(a.time * 1.7) * 0.35;
        return;
      }
      const phase = a.phase + a.time * 0.14;
      a.mesh.position.z = a.center + Math.sin(phase) * 6;
      // Near a bus bay on their side, walkers take the path behind it.
      let laneX = 5.2 + (a.targetLane ?? a.lane ?? 0) * 1.1, bayed = false;
      for (const bay of state.busBays || []) {
        if (!bay.mesh.parent) continue;
        const local = a.seg.worldToLocal(bay.mesh.parent.localToWorld(bay.center.clone()));
        if (Math.sign(local.x) !== Math.sign(a.mesh.position.x || 1)) continue;
        // Round the pocket along the curved pavement, in single file.
        const k = bayProfile(local.z - a.mesh.position.z);
        if (k > 0) { laneX = laneX + (8.55 - laneX) * k; bayed = true; break; }
      }
      const targetX = Math.sign(a.mesh.position.x || 1) * laneX;
      a.mesh.position.x += (targetX - a.mesh.position.x) * (bayed ? 1 : Math.min(1, dt * 3));
      const direction = Math.cos(phase);
      a.mesh.rotation.y = direction >= 0 ? 0 : Math.PI;
      a.mesh.userData.legs.forEach((leg, i) => { leg.rotation.x = Math.sin(a.time * 5 + i * Math.PI) * 0.32 * Math.abs(direction); });
      if (a.mesh.userData.dog) a.mesh.userData.dog.userData.legs.forEach((leg, i) => { leg.rotation.x = Math.sin(a.time * 9 + i * Math.PI / 2) * 0.55 * Math.abs(direction); });
      a.mesh.userData.arms.forEach((arm, i) => { arm.rotation.x = Math.sin(a.time * 5 + i * Math.PI) * -0.2 * Math.abs(direction); });
    });
    // One world-space snapshot makes following independent of actor order and
    // works after turns/rebasing, where neighbouring tasks have different parents.
    const traffic = new Map(state.actors.filter(a => !a.done && !a.fall).map(a =>
      [a, { box: actorFootprint(a), speed: a.active && !a.crashed ? a.speed : 0 }]));
    // The player's car is a leader too: traffic behind it brakes to a gap
    // (e.g. while the player waits at a question) instead of ramming it.
    const playerLeader = { config: { type: 'player' }, done: false, fall: false };
    traffic.set(playerLeader, { box: playerFootprint(), speed: Math.max(0, state.speed) });
    const currentBoxes = new Map([...traffic].filter(([a]) => a !== playerLeader).map(([a, entry]) => [a, entry.box]));
    state.actors.forEach(a => {
      if (a.done) return;
      if (a.fall) { updateActorFall(a, dt); return; }
      if (a.crashed) {
        a.speed = 0;
        if (a.knock) {
          const k = a.knock; k.t += dt;
          const u = Math.min(1, k.t / k.duration), e = 1 - Math.pow(1 - u, 3);
          a.mesh.position.lerpVectors(k.from, k.to, e);
          a.mesh.rotation.y = k.fromYaw + (k.toYaw - k.fromYaw) * e;
          if (u >= 1) a.knock = null;
        }
        if (actorFootprint(a).p.distanceTo(playerCarGroup.position) > 90 && !actorInView(a.mesh)) {
          a.done = true;
          a.mesh.visible = false;
        }
        return;
      }
      // staysPut: held by a traffic controller's signal (6.10) for good; it
      // blocks nobody's turn and is removed once far behind, out of view.
      if (a.config.staysPut) {
        a.cleared = true;
        if (actorFootprint(a).p.distanceTo(playerCarGroup.position) > 90 && !actorInView(a.mesh)) { a.done = true; a.mesh.visible = false; }
        return;
      }
      if (!a.active && !a.waitsForPlayer && a.dependencies?.every(b => b.cleared)) a.active = true;
      if (!a.active || a.done) return;
      // held: standing at the stop point, the way is clear for the player.
      a.held = !!a.holdFor && a.stopAtDistance !== undefined && a.distance >= a.stopAtDistance && holdPending(a);
      if (a.held) {
        a.speed = 0;
        return;
      }
      if (a.stopAtDistance !== undefined && a.distance >= a.stopAtDistance && a.stopFor > 0) {
        a.stopFor -= dt;
        a.speed = 0;
        return;
      }
      a.speed = Math.min(followingSpeed(a, traffic, dt), a.speed + dt * (a.config.type === 'pedestrian' ? 8 : 12));
      const advance = a.speed * dt;
      const steps = Math.max(1, Math.ceil(advance / 0.15));
      for (let i = 0; i < steps; i++) {
        const before = a.mesh.position.clone(), yaw = a.mesh.rotation.y, distance = a.distance;
        a.distance += advance / steps;
        const t = Math.min(1, a.distance / a.length), tangent = a.path.getTangentAt(t);
        a.mesh.position.copy(a.path.getPointAt(t));
        if (a.distance > a.length) a.mesh.position.addScaledVector(tangent, a.distance - a.length);
        a.mesh.rotation.y = Math.atan2(tangent.x, tangent.z);
        applyDetour(a, advance / steps);
        const box = actorFootprint(a);
        const playerContact = footprintsOverlap(box, playerFootprint(), 0.04);
        let trafficContact = false;
        for (const [b, other] of currentBoxes) {
          if (b !== a && !b.done && footprintsOverlap(box, other, 0.04)) { trafficContact = true; break; }
        }
        if (playerContact || trafficContact) {
          a.mesh.position.copy(before); a.mesh.rotation.y = yaw; a.distance = distance; a.speed = 0;
          if (playerContact && !state.attract && (!state.isAtSituation || state.resolution?.phase === 'manual')) {
            handleCollision(a, 'collision:' + a.config.id);
          }
          if (a.fall) currentBoxes.delete(a);
          else currentBoxes.set(a, actorFootprint(a));
          break;
        }
        currentBoxes.set(a, box);
      }
      const t = Math.min(1, a.distance / a.length);
      a.gait += a.speed * dt * 3.5;
      if (a.mesh.userData.legs) a.mesh.userData.legs.forEach((leg, i) => {
        leg.rotation.x = Math.sin(a.gait + i * Math.PI) * 0.42;
      });
      spinActorWheels(a.mesh, a.speed * dt);
      if (a.mesh.userData.pedals) a.mesh.userData.pedals.rotation.x += a.speed * dt * 1.8;
      a.cleared = a.crashed || !!a.fall || a.distance >= a.clearDistance;
      // Keep walking/riding beyond the planned path. Removal is permitted only
      // once the WHOLE actor is outside the camera, never at a fixed timer/distance.
      if (t >= 1 && !actorInView(a.mesh)) { a.done = true; a.mesh.visible = false; }
    });
  }

  function actorInView(mesh) {
    // Only the actor's ancestor chain and subtree need fresh matrices here.
    // Updating every prebuilt district for each departing actor is quadratic.
    mesh.updateWorldMatrix(true, true);
    camera.updateMatrixWorld(true);
    const frustum = new THREE.Frustum().setFromProjectionMatrix(
      new THREE.Matrix4().multiplyMatrices(camera.projectionMatrix, camera.matrixWorldInverse));
    return frustum.intersectsBox(new THREE.Box3().setFromObject(mesh).expandByScalar(3));
  }

  function startActorFall(actor) {
    if (actor.fall || !['pedestrian', 'cyclist'].includes(actor.config.type)) return;
    const relativeYaw = playerCarGroup.rotation.y + (state.speed < 0 ? Math.PI : 0) - actorFootprint(actor).yaw;
    const push = new THREE.Vector3(Math.sin(relativeYaw), 0, Math.cos(relativeYaw));
    actor.fall = { time: 0, clearTime: 0, direction: Math.sin(relativeYaw) >= 0 ? 1 : -1,
      push, axis: new THREE.Vector3(push.z, 0, -push.x),
      impulse: Math.min(1.2, Math.max(0.25, Math.abs(state.speed) * 0.08)) };
    actor.speed = 0;
    actor.cleared = true;
    actor.done = false;
    actor.mesh.visible = true;
    actor.mesh.userData.badge.visible = false;
  }

  function updateActorFall(actor, dt) {
    const fall = actor.fall;
    fall.time += dt;
    const body = actor.mesh.userData.body;
    const dropping = Math.min(1, fall.time / 0.65);
    // A struck pedestrian/cyclist stays down for the rest of the scene and
    // has no collision shape: the run can never get stuck on them.
    const amount = Math.sin(dropping * Math.PI / 2);
    if (actor.config.type === 'cyclist') body.quaternion.setFromAxisAngle(new THREE.Vector3(0, 0, 1), fall.direction * amount * 1.5);
    else body.quaternion.setFromAxisAngle(fall.axis, amount * 1.48);
    body.position.x = fall.push.x * fall.impulse * amount;
    body.position.z = fall.push.z * fall.impulse * amount;
    body.position.y = 0;
    if (actor.mesh.userData.legs) actor.mesh.userData.legs.forEach((leg, i) => {
      leg.rotation.x = amount * (i ? -0.55 : 0.35);
    });
    if (actor.mesh.userData.arms) actor.mesh.userData.arms.forEach((arm, i) => {
      arm.rotation.z = (i ? 1 : -1) * (0.1 + amount * 0.8);
      arm.rotation.x = -amount * 0.5;
    });
    if (actor.mesh.userData.rider) {
      const rider = actor.mesh.userData.rider;
      rider.position.z = amount * 0.45;
      rider.rotation.x = -amount * 0.4;
      rider.rotation.z = -fall.direction * amount * 0.2;
    }
    // Ground contact prevents limbs/bicycle sinking through the road. A small
    // damped rebound communicates inertia without violence or injury effects.
    actor.mesh.updateMatrixWorld(true);
    const bounds = new THREE.Box3().setFromObject(body);
    const groundY = actor.mesh.getWorldPosition(new THREE.Vector3()).y;
    body.position.y = Math.max(0, groundY - bounds.min.y) +
      (fall.time < 0.65 ? Math.sin(dropping * Math.PI) * 0.12 : 0);
    if (fall.time > 2 && actorFootprint(actor).p.distanceTo(playerCarGroup.position) > 90 && !actorInView(actor.mesh)) {
      actor.done = true;
      actor.mesh.visible = false;
    }
  }

  function footprintsOverlap(a, b, margin = 0) {
    const axes = box => [new THREE.Vector3(Math.cos(box.yaw), 0, -Math.sin(box.yaw)),
      new THREE.Vector3(Math.sin(box.yaw), 0, Math.cos(box.yaw))];
    const aa = axes(a), bb = axes(b), delta = b.p.clone().sub(a.p);
    return [...aa, ...bb].every(axis => {
      const ra = Math.abs(axis.dot(aa[0])) * a.halfWidth + Math.abs(axis.dot(aa[1])) * a.halfLength;
      const rb = Math.abs(axis.dot(bb[0])) * b.halfWidth + Math.abs(axis.dot(bb[1])) * b.halfLength;
      return Math.abs(delta.dot(axis)) < ra + rb + margin;
    });
  }

  function playerFootprint() {
    return { p: playerCarGroup.position, yaw: playerCarGroup.rotation.y,
      halfWidth: playerCarGroup.userData.halfWidth, halfLength: playerCarGroup.userData.halfLength };
  }

  function actorFootprint(actor) {
    const p = actor.mesh.getWorldPosition(new THREE.Vector3());
    const q = actor.mesh.getWorldQuaternion(new THREE.Quaternion());
    const forward = new THREE.Vector3(0, 0, 1).applyQuaternion(q);
    let halfWidth = actor.halfWidth, halfLength = actor.halfLength;
    if (actor.fall) {
      // The visible body is displaced by the impact inside the actor group.
      // Fallen actors take part in no collision test; this footprint is only
      // used to keep traffic from spawning/driving through the visible body.
      const body = actor.mesh.userData.body;
      p.add(new THREE.Vector3(body.position.x, 0, body.position.z).applyQuaternion(q));
    }
    return { p, yaw: Math.atan2(forward.x, forward.z), halfWidth, halfLength };
  }

  function pathsConflict(a, b) {
    if (a.config?.concurrentWith?.includes('player') || b.config?.concurrentWith?.includes('player')) return false;
    if (a.config?.concurrentWith?.includes(b.config?.id) || b.config?.concurrentWith?.includes(a.config?.id)) return false;
    const samples = motion => {
      const points = [];
      for (let d = 0; d <= Math.min(motion.length, motion.clearDistance + 5); d += 1) {
        const t = d / motion.length, v = motion.path.getTangentAt(t);
        points.push({ p: motion.path.getPointAt(t), yaw: Math.atan2(v.x, v.z),
          halfWidth: motion.halfWidth, halfLength: motion.halfLength });
      }
      return points;
    };
    const aa = samples(a), bb = samples(b);
    return aa.some(p => bb.some(q => footprintsOverlap(p, q, 0.2)));
  }

  let mistakeHighlightMesh = null;

  function highlightMistake(details = {}) {
    clearMistakeHighlight();
    const group = new THREE.Group();
    group.userData.mistakeHighlight = true;

    const ringGeo = new THREE.RingGeometry(1.8, 3.6, 32);
    ringGeo.rotateX(-Math.PI / 2);
    const ringMat = new THREE.MeshBasicMaterial({
      color: 0xEF4444,
      transparent: true,
      opacity: 0.75,
      side: THREE.DoubleSide,
      depthWrite: false
    });
    const ring = new THREE.Mesh(ringGeo, ringMat);
    ring.position.y = 0.04;
    group.add(ring);

    const innerGeo = new THREE.CircleGeometry(1.75, 32);
    innerGeo.rotateX(-Math.PI / 2);
    const innerMat = new THREE.MeshBasicMaterial({
      color: 0xF87171,
      transparent: true,
      opacity: 0.28,
      side: THREE.DoubleSide,
      depthWrite: false
    });
    const innerDisc = new THREE.Mesh(innerGeo, innerMat);
    innerDisc.position.y = 0.038;
    group.add(innerDisc);

    const pos = details.position || playerCarGroup.position;
    group.position.set(pos.x, 0, pos.z);
    scene.add(group);
    mistakeHighlightMesh = { group, ringMat, innerMat, elapsed: 0, duration: 1.8 };
  }

  function clearMistakeHighlight() {
    if (mistakeHighlightMesh) {
      scene.remove(mistakeHighlightMesh.group);
      mistakeHighlightMesh.group.traverse(o => {
        if (o.geometry) o.geometry.dispose();
        if (o.material) o.material.dispose();
      });
      mistakeHighlightMesh = null;
    }
  }

  function updateMistakeHighlight(dt) {
    if (!mistakeHighlightMesh) return;
    const mh = mistakeHighlightMesh;
    mh.elapsed += dt;
    if (mh.elapsed >= mh.duration) {
      clearMistakeHighlight();
      return;
    }
    const progress = mh.elapsed / mh.duration;
    const pulse = 1.0 + 0.12 * Math.sin(mh.elapsed * 12);
    mh.group.scale.set(pulse, 1, pulse);
    const fade = Math.max(0, 1 - Math.pow(progress, 2));
    mh.ringMat.opacity = 0.75 * fade;
    mh.innerMat.opacity = 0.28 * fade;
  }

  function drivingFault(type, key = type) {
    const r = state.resolution;
    const faults = r ? r.faults : state.driveFaults;
    if (faults.has(key)) return;
    faults.add(key);
    highlightMistake({ type });
    sendToFlutter({ event: 'violation', type, episode: ++state.violationEpisode });
  }

  function placeActorAtDistance(actor, distance) {
    actor.distance = Math.max(0, distance);
    const t = Math.min(1, actor.distance / actor.length);
    const tangent = actor.path.getTangentAt(t);
    actor.mesh.position.copy(actor.path.getPointAt(t));
    if (distance < 0) actor.mesh.position.addScaledVector(actor.path.getTangentAt(0), distance);
    else if (actor.distance > actor.length) actor.mesh.position.addScaledVector(tangent, actor.distance - actor.length);
    actor.mesh.rotation.y = Math.atan2(tangent.x, tangent.z);
  }

  function playerContacts(margin = 0) {
    return new Set(state.actors.filter(a => !a.done && !a.fall &&
      footprintsOverlap(playerFootprint(), actorFootprint(a), margin)));
  }

  function separateCrashedActor(actor) {
    // Guarantee a usable escape gap: first back the vehicle along its own
    // route, then (if the route itself runs into the player) push it straight
    // away from the player's car. An unresolved overlap would re-trigger the
    // collision every frame, freezing the run even when trying to reverse.
    // The vehicle does not teleport: it slides to the resting spot (a.knock).
    if (!actor || ['pedestrian', 'cyclist'].includes(actor.config.type)) return;
    // Wide enough to steer around the wreck from a standstill.
    const gap = 0.9;
    if (!footprintsOverlap(playerFootprint(), actorFootprint(actor), gap)) return;
    const startPosition = actor.mesh.position.clone(), startYaw = actor.mesh.rotation.y;
    const finish = () => {
      actor.knock = { from: startPosition, fromYaw: startYaw, to: actor.mesh.position.clone(), toYaw: actor.mesh.rotation.y, t: 0, duration: 0.34 };
      actor.mesh.position.copy(startPosition); actor.mesh.rotation.y = startYaw;
    };
    const originalDistance = actor.distance;
    for (let retreat = 0.2; retreat <= 6; retreat += 0.2) {
      placeActorAtDistance(actor, originalDistance - retreat);
      if (!footprintsOverlap(playerFootprint(), actorFootprint(actor), gap)) { finish(); return; }
    }
    placeActorAtDistance(actor, originalDistance);
    const away = actorFootprint(actor).p.clone().sub(playerCarGroup.position); away.y = 0;
    if (away.lengthSq() < 1e-4) away.set(Math.cos(playerCarGroup.rotation.y), 0, -Math.sin(playerCarGroup.rotation.y));
    away.normalize();
    const parent = actor.mesh.parent;
    const localAway = parent ? away.clone().transformDirection(parent.matrixWorld.clone().invert()) : away;
    for (let push = 0.1; push <= 8; push += 0.1) {
      actor.mesh.position.addScaledVector(localAway, 0.1);
      actor.mesh.updateMatrixWorld(true);
      if (!footprintsOverlap(playerFootprint(), actorFootprint(actor), gap)) { finish(); return; }
    }
    finish();
  }

  function parkCrashedActor(actor) {
    if (!actor || actor.crashed || ['pedestrian', 'cyclist'].includes(actor.config.type)) return;
    separateCrashedActor(actor);
    // After a crash: turn signals off, hazard lights on (п. 7.1).
    actor.signalPlan = null;
    actor.mesh.userData.blinkerSide = 'hazard';
    actor.speed = 0;
    actor.active = false;
    actor.crashed = true;
    actor.cleared = true;
  }

  function handleCollision(actor, key) {
    if (['pedestrian', 'cyclist'].includes(actor.config.type)) gameAudio?.softImpact(actor.config.type);
    else gameAudio?.impact(Math.abs(state.speed));
    startActorFall(actor);
    parkCrashedActor(actor);
    resetAfterImpact('collision', key);
  }

  function resetAfterImpact(type, key) {
    drivingFault(type, key);
    if (type === 'collision') { state.hazard = 8; state.blinker = null; }
    state.speed = 0;
    state.isAccelerating = false;
    state.isBraking = false;
    // Simple mode keeps the planned route through the junction for after the
    // control release: the car stands still on it meanwhile (no teleport).
    if (state.resolution && state.simpleSteering && state.autoPath) state.resolution.pausedPath = state.autoPath;
    state.steering = 0; state.laneChangeX = null; state.autoPath = null;
    // A short control release makes the impact legible, but never teleports or
    // rotates the player's car. After it expires the player can immediately
    // steer around the stationary crash participant.
    if (state.resolution) state.resolution.recovery = 0.38;
    else state.driveRecovery = 0.38;
    sendToFlutter({ event: 'maneuver_reset' });
  }

  function updateResolution(dt) {
    const r = state.resolution;
    if (!r) return;
    r.elapsed += dt;
    if (r.recovery > 0) {
      if (r.pathAudit) r.pathAudit.previous.copy(playerCarGroup.position);
      r.recovery = Math.max(0, r.recovery - dt);
      if (!r.recovery) {
        r.faults.delete('offroad');
        r.motions.forEach(a => r.faults.delete('collision:' + a.config.id));
        // Back on the route the player chose (simple mode): without it the
        // car ran straight on past the turn — the choice is closed by then —
        // and collected a wrong-manoeuvre fault on top of the crash.
        if (r.pausedPath) { state.autoPath = r.pausedPath; r.pausedPath = null; }
        sendToFlutter({ event: 'maneuver_ready' });
      }
      return;
    }
    const evidence = r.intersection.situation;
    if (evidence.redWait && r.elapsed >= evidence.redWait) r.intersection.trafficLight.setLightState('green');
    const contactsBefore = playerContacts();
    // Separate signals (13.7, ticket 26·13): past the first carriageway the
    // car stops at the median stop line until its own light turns green —
    // two seconds of standing there.
    let medianHold = false;
    const medianLight = r.intersection.situation.hasMedianStopLine && r.intersection.seg?.userData.medianTrafficLight;
    if (medianLight && !r.medianGreen) {
      const car=playerCarGroup,alongX=r.intersection.situation.geometry==='divided_main';
      const line=alongX ? (r.intersection.situation.medianStopX??r.intersection.kerbX+.6) : r.intersection.centerZ+2;
      const front=alongX ? car.position.x+Math.sin(car.rotation.y)*(car.userData.halfLength||2) : car.position.z+Math.cos(car.rotation.y)*(car.userData.halfLength||2);
      const onLine=alongX ? car.position.z-r.intersection.centerZ>-.6&&car.position.z-r.intersection.centerZ<4.6&&Math.sin(car.rotation.y)>.3 : car.position.x>-4.6&&car.position.x<.6&&Math.cos(car.rotation.y)>.3;
      if (onLine && front >= line - 0.4 && front < line + 1.5) {
        medianHold = state.speed >= 0;
        r.medianWait = (r.medianWait || 0) + (Math.abs(state.speed) < 0.3 ? dt : 0);
        if (r.medianWait >= 2) { r.medianGreen = true; medianLight.setLightState('green'); medianHold = false; }
      }
    }
    if (medianHold) state.speed = 0;
    // No exit chosen at a T-junction: wait at the turn for an arrow (the gas
    // stays held, so the car moves off the moment a side is picked).
    const waitForExit = state.simpleSteering && r.simpleOpen && !r.simpleChoice &&
      playerCarGroup.position.z >= r.simpleGate - 0.5 && state.speed >= 0;
    if (waitForExit) state.speed = 0;
    if (r.simpleOpen && playerCarGroup.position.z > r.simpleGate && r.simpleChoice) r.simpleOpen = false;
    if (state.replanExit && state.speed > 0 && state.simpleSteering) {
      state.replanExit = false;
      if (r.simpleChoice && !state.autoPath) applyJunctionChoice(r);
    }
    integrateDriving(dt, waitForExit || medianHold ? 0 : state.maxSpeed);
    if (evidence.requiredStop !== undefined) {
      const line = r.intersection.centerZ + evidence.requiredStop;
      if (!evidence.redWait) checkRequiredStop(r, line, dt, type => drivingFault(type));
      const front = playerCarGroup.position.z + Math.cos(playerCarGroup.rotation.y) * playerCarGroup.userData.halfLength;
      if (evidence.redWait && r.elapsed < evidence.redWait && front > line + 0.25) drivingFault('red_light');
    }
    reportExit(r);
    checkManeuverPath(r);
    if (r.recovery > 0) return;
    const p = playerCarGroup.position, z = r.intersection.centerZ, yaw = playerCarGroup.rotation.y;
    const playerBox = { p, yaw, halfWidth: playerCarGroup.userData.halfWidth, halfLength: playerCarGroup.userData.halfLength };
    for (const a of r.motions) {
      if (a.done || a.fall) continue;
      const other = actorFootprint(a);
      if (footprintsOverlap(playerBox, other)) {
        // A contact that already existed at the start of the frame is being
        // resolved (the player is driving out of it) — never a new ДТП.
        if (contactsBefore.has(a)) { if (a.crashed && !a.knock) separateCrashedActor(a); continue; }
        // Nudging a car already standing after a crash is not a new ДТП.
        if (a.crashed && !a.fall) continue;
        handleCollision(a, 'collision:' + a.config.id);
        return;
      }
      if (state.speed > 0.5 && r.yielding.includes(a) && !a.cleared) {
        if (r.spec.staged && r.spec.waitInside && p.z < z - 1.5 && Math.abs(p.x) < 2.5) {
          // Staged maneuver: driver enters intersection and waits before turning path
        } else if (conflictAhead(playerBox, a)) drivingFault('priority');
      }
    }
    const sideStreet = Math.abs(p.x) > 7;
    const mainStreet = Math.abs(p.z - z) > 7;
    const oneWay = r.intersection.situation.oneWay;
    if (oneWay && sideStreet) {
      // A one-way cross street has no oncoming lane: with its flow any lane
      // is legal (8.6 is judged by the question, not here), against it is
      // driving against the flow whatever the lane.
      const flowSide = oneWay === 'to_right' ? -1 : 1; // world X of the flow's exit
      const heading = Math.sign(Math.sin(yaw)) || 1;
      updateLaneViolation(dt, false, heading !== flowSide);
    } else {
      if(r.intersection.situation.junctionLayout) {
        const arms=[...r.intersection.situation.junctionLayout.arms,{exit:'uturn',x:0,z:-26,yaw:Math.PI}];
        let frame=null,best=Infinity;
        for(const a of arms) {
          const f=new THREE.Vector3(Math.sin(a.yaw),0,Math.cos(a.yaw)),delta=new THREE.Vector3(p.x,0,p.z-z);
          const along=delta.dot(f),offset=delta.x*f.z-delta.z*f.x;
          if(along>10&&Math.abs(offset)<best){best=Math.abs(offset);frame={offset,yaw:a.yaw};}
        }
        updateLaneViolation(dt,frame ? Math.cos(yaw-frame.yaw)*frame.offset>.85 : false);
      } else {
        const sideOffset=p.z-z-(r.spec.exitOffsets?.[p.x<0?'right':'left']||0);
        updateLaneViolation(dt,sideStreet ? Math.sin(yaw)*sideOffset<-.85 : mainStreet&&Math.cos(yaw)*p.x>.85);
      }
    }
    const exits = [
      ['left', Math.PI / 2, p.x > 24, Math.abs(p.z - z - (r.spec.exitOffsets?.left || 0)), p.x > 40],
      ['right', -Math.PI / 2, p.x < -24, Math.abs(p.z - z - (r.spec.exitOffsets?.right || 0)), p.x < -40],
      ['straight', 0, p.z > z + 24, Math.abs(p.x), p.z > z + 40],
      ['uturn', Math.PI, p.z < z - 24, Math.abs(p.x), p.z < z - 40],
    ];
    if(r.intersection.situation.junctionLayout) {
      exits.length=0;
      for(const a of [...r.intersection.situation.junctionLayout.arms,{exit:'uturn',x:0,z:-26,yaw:Math.PI}]) {
        const f=new THREE.Vector3(Math.sin(a.yaw),0,Math.cos(a.yaw)),delta=new THREE.Vector3(p.x,0,p.z-z),along=delta.dot(f),lateral=Math.abs(delta.x*f.z-delta.z*f.x);
        const mouth=Math.hypot(a.x,a.z);exits.push([a.exit,a.yaw,along>mouth-8,lateral,along>mouth+8]);
      }
    }
    for (const [direction, heading, beyond, lateral, farBeyond] of exits) {
      const error = Math.atan2(Math.sin(yaw - heading), Math.cos(yaw - heading));
      // Any position on the exit's carriageway counts (a car hugging the far
      // kerb, or still straightening out). Well past the junction the exit is
      // taken whatever the heading: the preview roads end after 200 m, and a
      // missed hand-over used to leave the player in a dead end.
      const sideExit = direction === 'left' || direction === 'right';
      const width = sideExit && r.intersection.halfW ? r.intersection.halfW(p.x) + 0.1 : 4.3;
      const footprintWidth=playerCarGroup.userData.halfWidth*Math.abs(Math.cos(error))+playerCarGroup.userData.halfLength*Math.abs(Math.sin(error));
      const fitsExit=lateral+footprintWidth<=4.2+SEAM;
      if ((beyond && fitsExit && lateral < width && Math.abs(error) < 0.7) || (farBeyond && lateral < width + 1.7 && Math.abs(error) < Math.PI / 2)) {
        r.exitDirection = direction;
        r.exitYaw = heading;
        if (!(r.spec.allowedManeuvers || [r.spec.maneuver]).includes(direction)) drivingFault('wrong_maneuver');
        finishManeuver();
        break;
      }
    }
  }

  // Source-authored lawful corridors, sampled once. Judge the swept motion,
  // not merely the exit: cutting across a prohibited carriageway or tracks
  // and returning to the correct lane must still be detected.
  function buildManeuverAudit(r) {
    const origin = r.intersection.centerZ;
    return {
      previous: playerCarGroup.position.clone(),
      paths: r.spec.pathRules.paths.map(def => {
        const path = curve([r.entry.clone(), ...def.points.map(([x,z]) => new THREE.Vector3(x,0,origin+z))]);
        const n = Math.max(2, Math.ceil(path.getLength() / 0.35));
        const points=path.getSpacedPoints(n);
        return {maneuver:def.maneuver,valid:true,segments:points.slice(1).map((p,i)=>{const a=points[i],dx=p.x-a.x,dz=p.z-a.z;return [a.x,a.z,dx,dz,dx*dx+dz*dz];})};
      })
    };
  }

  function checkManeuverPath(r) {
    const audit = r.pathAudit;
    if (!audit || r.recovery > 0) return;
    const p = playerCarGroup.position, old = audit.previous;
    // Some source questions constrain one manoeuvre while also allowing a
    // straight continuation. Do not force that driver to take the pictured turn.
    const only = r.spec.pathRules.onlyManeuvers;
    const yaw = playerCarGroup.rotation.y;
    const actual = r.simpleChoice || (Math.cos(yaw) < -0.3 ? 'uturn' : Math.sin(yaw) > 0.35 ? 'left' : Math.sin(yaw) < -0.35 ? 'right' : 'straight');
    if (only && !only.includes(actual)) { old.copy(p); return; }
    const tolerance = r.spec.pathRules.tolerance || 1.45;
    const distance = old.distanceTo(p), steps = Math.max(1, Math.ceil(distance / 0.4));
    const q = new THREE.Vector3();
    for (let i=1; i<=steps; i++) {
      q.lerpVectors(old,p,i/steps);
      // Once the whole car has finished the turn, changing to another lane
      // is judged by its actual markings/traffic, not the demonstration path.
      if (r.spec.pathRules.turnOnly && Math.abs(q.x) > (r.intersection.kerbX || 4.2) + playerCarGroup.userData.halfLength + 4) continue;
      for (const path of audit.paths) {
        if (!path.valid) continue;
        path.valid = path.segments.some(([ax,az,dx,dz,len2]) => {
          const u=len2 ? THREE.MathUtils.clamp(((q.x-ax)*dx+(q.z-az)*dz)/len2,0,1) : 0;
          return (q.x-ax-u*dx)**2+(q.z-az-u*dz)**2 <= tolerance*tolerance;
        });
      }
      if (!audit.paths.some(path=>path.valid)) { drivingFault('wrong_maneuver'); break; }
    }
    old.copy(p);
  }

  // Would the player, keeping speed and heading, get in the way of a
  // participant it must give way to within the next second? The participant
  // is followed along its own route: a turning vehicle sweeps across the
  // player's path where a straight extrapolation of it would not (13_15).
  function conflictAhead(playerBox, a) {
    const forward = new THREE.Vector3(Math.sin(playerBox.yaw), 0, Math.cos(playerBox.yaw));
    const planned = state.autoPath;
    a.mesh.parent.updateWorldMatrix(true, false);
    const toWorld = a.mesh.parent.matrixWorld;
    for (const t of [0.25, 0.5, 0.75, 1]) {
      const u = Math.min(1, (a.distance + a.speed * t) / a.length);
      const tangent = a.path.getTangentAt(u).transformDirection(toWorld);
      const other = { p: a.path.getPointAt(u).applyMatrix4(toWorld), yaw: Math.atan2(tangent.x, tangent.z),
        halfWidth: a.halfWidth, halfLength: a.halfLength };
      // Simple steering drives a planned curve: predict along it, not along
      // the heading (a turning car does not go straight on).
      let mine;
      if (planned) {
        const v = Math.min(1, (planned.s + state.speed * t) / planned.length), tan = planned.path.getTangentAt(v);
        mine = { ...playerBox, p: planned.path.getPointAt(v), yaw: Math.atan2(tan.x, tan.z) };
      } else mine = { ...playerBox, p: playerBox.p.clone().addScaledVector(forward, state.speed * t) };
      if (footprintsOverlap(mine, other, 0.5)) return true;
    }
    return false;
  }

  function finishManeuver() {
    state.laneChangeX = null; state.autoPath = null; state.trail = [];
    const r = state.resolution;
    if (!r) return;
    const trailing = r.motions.filter(a => !r.yielding.includes(a));
    trailing.forEach(a => { a.waitsForPlayer = false; });
    const id = r.intersection.situation.id;
    state.district = (state.district + 1) % DISTRICTS;
    r.intersection.guide.visible = false;
    state.intersections = state.intersections.filter(i => i !== r.intersection);
    const outgoingPreview = r.intersection.previews[r.exitDirection || r.spec.maneuver];
    scene.updateMatrixWorld(true);
    const roadWorld = outgoingPreview.matrixWorld.clone();
    const ends = outgoingPreview.userData.roadEnds.map(p => p.clone().applyMatrix4(roadWorld));
    scene.add(outgoingPreview);
    roadWorld.decompose(outgoingPreview.position, outgoingPreview.quaternion, outgoingPreview.scale);
    state.roadSegments.push(outgoingPreview);
    let transform = new THREE.Matrix4();
    if (r.exitYaw !== 0) {
      // Rebase the whole visible world, including the camera, without a visual cut.
      // New road geometry can then continue along local +Z after any number of turns.
      const forward = new THREE.Vector3(Math.sin(r.exitYaw), 0, Math.cos(r.exitYaw));
      const center = new THREE.Vector3().setFromMatrixPosition(roadWorld);
      const endpoint = center.clone().addScaledVector(forward, playerCarGroup.position.clone().sub(center).dot(forward));
      const rotation = new THREE.Matrix4().makeRotationY(-r.exitYaw);
      transform = rotation.multiply(new THREE.Matrix4().makeTranslation(-endpoint.x, 0, -endpoint.z));
      state.roadSegments.forEach(seg => seg.applyMatrix4(transform));
      window.PDD_ROADS.rebase(transform);
      const oldPlanes = new Set();
      state.roadSegments.forEach(seg => seg.traverse(obj => {
        for (const p of obj.material?.clippingPlanes || []) oldPlanes.add(p);
      }));
      oldPlanes.forEach(p => p.applyMatrix4(transform));
      camera.position.applyMatrix4(transform);
      cameraLook.applyMatrix4(transform);
      cameraHeading -= r.exitYaw;
      playerCarGroup.position.applyMatrix4(transform);
      playerCarGroup.rotation.y -= r.exitYaw;
      state.intersections = [];
    }
    ends.forEach(p => p.applyMatrix4(transform));
    const boundary = Math.min(...ends.map(p => p.z));
    nextSegmentZ = Math.max(...ends.map(p => p.z));
    state.exitRoad = outgoingPreview;
    currentCorridor = outgoingPreview;
    state.sideJunction = null;
    state.oneWayAgainst = false;
    // The outgoing road owns everything past this seam. Retired cross streets
    // cannot cut through future junctions even after several turns or U-turns.
    const cut = new THREE.Plane(new THREE.Vector3(0, 0, -1), boundary);
    state.roadSegments.filter(seg => seg !== outgoingPreview).forEach(seg => seg.traverse(obj => {
      if (obj.userData.sceneryObject) {
        const box = new THREE.Box3().setFromObject(obj);
        if (box.max.z > boundary) obj.visible = false;
      }
      let root = obj;
      while (root) { if (root.userData.sceneryObject) return; root = root.parent; }
      if (obj.userData.actor || obj.userData.tramRail || !obj.material) return;
      const clip = material => {
        const copy = cloneMaterial(material);
        (obj.userData.replacedMaterials ||= new Set()).add(material);
        copy.clippingPlanes = [...(material.clippingPlanes || []), cut];
        copy.clipShadows = true;
        return copy;
      };
      obj.material = Array.isArray(obj.material) ? obj.material.map(clip) : clip(obj.material);
    }));
    refreshRoadBounds();
    state.currentLaneOffset = playerCarGroup.position.x;
    state.targetLaneOffset = state.currentLaneOffset > 0 ? 1.8 : -1.8;
    state.targetLane = state.currentLaneOffset > 0 ? 0 : 1;
    state.lastSafePosition.copy(playerCarGroup.position);
    state.lastSafeYaw = playerCarGroup.rotation.y;
    // Entering a one-way road against its flow stays one ongoing violation.
    if (state.targetLane === 1 && outgoingPreview.userData.oneWay !== 'against') clearOncoming();
    state.isAtSituation = false;
    state.isResolvingSituation = false;
    state.activeIntersection = null;
    state.resolution = null;
    if (!state.speedZoneActive) state.speedLimitKmH = null;
    else {
      state.carriedZoneEndZ = playerCarGroup.position.z + 120;
      addRoadSign(outgoingPreview, '5.32', outgoingPreview.worldToLocal(new THREE.Vector3(0,0,state.carriedZoneEndZ)).z);
    }
    state.motorwayEndZ = null;
    state.speedingTime = 0;
    state.speedingPenalized = false;
    const junctionSigns = r.intersection.situation.signs || [];
    if ((r.exitDirection || r.spec.maneuver) === 'straight' && junctionSigns.some(sg => sg.code === '5.1')) {
      // Past a 5.1 the player may actually drive at motorway speed; a 5.2
      // further on ends the stretch and the town limit comes back.
      state.speedLimitKmH = 110;
      state.motorwayEndZ = playerCarGroup.position.z + 170;
    }
    placeRoadEvent(boundary);
    if (state.motorwayEndZ != null) {
      // The stretch ends well before the next road question.
      const nextStop = state.roadEvent?.stopZ;
      if (nextStop != null) state.motorwayEndZ = Math.max(playerCarGroup.position.z + 50, Math.min(state.motorwayEndZ, nextStop - 30));
      const end = createRoadSign('5.2');
      end.position.copy(outgoingPreview.worldToLocal(new THREE.Vector3(-5.6, 0, state.motorwayEndZ)));
      end.userData.signCode = '5.2';
      outgoingPreview.add(end);
    }
    // Populate the exit in this same update, not after the next rendered frame.
    checkAndSpawnNext();
    reportExit(null);
    sendToFlutter({ event: 'situation_cleared', situationId: id });
  }

  // --- Straight-road situations: speed limits, overtaking, pedestrian crossings ---
  // A road event lives in its own group that is transformed with the world
  // (it is listed in state.roadSegments), so world coordinates stay valid
  // across rebases. Driver's right is negative X, the player's lane is x=-1.8.
  let roadBag = [], lastRoadId = null;
  function nextRoadSituation() {
    const pool = window.PDD_ROAD_SITUATIONS || [];
    if (!pool.length) return null;
    if (!roadBag.length) {
      roadBag = pool.slice();
      for (let i = roadBag.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [roadBag[i], roadBag[j]] = [roadBag[j], roadBag[i]];
      }
      if (roadBag.length > 1 && roadBag[roadBag.length - 1].id === lastRoadId) {
        [roadBag[0], roadBag[roadBag.length - 1]] = [roadBag[roadBag.length - 1], roadBag[0]];
      }
    }
    const selected = roadBag.pop();
    lastRoadId = selected.id;
    return selected;
  }

  function createTextPlate(text) {
    const canvas = document.createElement('canvas');
    canvas.width = 240; canvas.height = 120;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#fafafa'; ctx.fillRect(0, 0, 240, 120);
    ctx.strokeStyle = '#20252a'; ctx.lineWidth = 8; ctx.strokeRect(5, 5, 230, 110);
    ctx.fillStyle = '#20252a'; ctx.font = 'bold 64px sans-serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(text, 120, 62);
    const face = new THREE.Mesh(new THREE.PlaneGeometry(1.25, 0.62),
      new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(canvas) }));
    face.position.z = ROAD_SIGN_FACE_Z;
    face.rotation.y = Math.PI;
    const group = new THREE.Group(); group.add(face);
    addSignBack(face);
    return group;
  }

  const roadMarkingMat = () => new THREE.MeshBasicMaterial({ color: BRAND.asphaltMarking });
  function addFlatPlane(group, width, length, x, z, y, material) {
    const mesh = new THREE.Mesh(new THREE.PlaneGeometry(width, length), material);
    mesh.rotation.x = -Math.PI / 2; mesh.position.set(x, y, z);
    mesh.receiveShadow = Boolean(material.isMeshLambertMaterial);
    if(material.color?.getHex()===BRAND.asphalt)material.userData.asphalt=true;
    group.add(mesh);
    return mesh;
  }
  // Replace the default broken centre line over [from, to] with the given
  // marking: 'solid' (1.1), 'double_solid_right' / 'double_dashed_right' (1.11,
  // the named line being the one on the player's side).
  function addCentreMarking(group, from, to, marking) {
    const cover = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
    // Clearly above the road's own paint (0.025): no z-fighting from the chase camera.
    addFlatPlane(group, 0.7, to - from, 0, (from + to) / 2, 0.034, cover);
    const paint = roadMarkingMat();
    const solid = x => addFlatPlane(group, 0.13, to - from, x, (from + to) / 2, 0.04, paint);
    const dashed = x => { const parts = []; for (let z = from + 1; z < to - 2; z += 5) parts.push(addFlatPlane(new THREE.Group(), 0.13, 2, x, z + 1, 0.04, paint)); group.add(mergeStatic(parts, paint)); };
    if (marking === 'solid') solid(0);
    else if (marking === 'double_solid_right') { solid(-0.14); dashed(0.14); }
    else if (marking === 'double_dashed_right') { dashed(-0.14); solid(0.14); }
  }
  function addZebra(group, z) {
    const cover = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
    addFlatPlane(group, 0.7, 5.2, 0, z, 0.034, cover);
    const paint = roadMarkingMat();
    const parts = []; for (let x = -3.6; x <= 3.6 + 0.01; x += 0.9) parts.push(addFlatPlane(new THREE.Group(), 0.45, 4, x, z, 0.04, paint));
    group.add(mergeStatic(parts, paint));
  }
  // Towns for the settlement signs 5.23.1 / 5.24.1: the town you leave and
  // the next one are always different places.
  const TOWNS = ['Липецк', 'Тверь', 'Калуга', 'Рязань', 'Тула', 'Владимир', 'Кострома', 'Ярославль', 'Псков', 'Орёл',
    'Курск', 'Брянск', 'Смоленск', 'Иваново', 'Вологда', 'Тамбов', 'Пенза', 'Саранск', 'Чебоксары', 'Киров',
    'Пермь', 'Уфа', 'Самара', 'Казань', 'Сызрань', 'Коломна', 'Серпухов', 'Дмитров', 'Суздаль', 'Ростов'];
  function townPair() {
    const a = Math.floor(Math.random() * TOWNS.length);
    const b = (a + 1 + Math.floor(Math.random() * (TOWNS.length - 1))) % TOWNS.length;
    return [TOWNS[a], TOWNS[b]];
  }
  function settlementTexture(code, town) {
    const key = code + ':' + town;
    let texture = signTextureCache.get(key);
    if (texture) return texture;
    const canvas = document.createElement('canvas'); canvas.width = 896; canvas.height = 200;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, 896, 200);
    ctx.strokeStyle = '#151515'; ctx.lineWidth = 14; ctx.strokeRect(14, 14, 868, 172);
    ctx.fillStyle = '#151515'; ctx.font = 'bold 118px Arial'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(town.toUpperCase(), 448, 106, 800);
    if (code === '5.24.1') { // end of the settlement: red diagonal across the name
      ctx.strokeStyle = '#cc1725'; ctx.lineWidth = 16;
      ctx.beginPath(); ctx.moveTo(40, 180); ctx.lineTo(856, 20); ctx.stroke();
    }
    texture = new THREE.CanvasTexture(canvas); signTextureCache.set(key, texture);
    return texture;
  }
  // A sign-artwork plate under a sign (1.4.x under 1.1/1.2): its own
  // proportions (tall), exact catalogue SVG.
  function createImagePlate(code, width = 0.62, aspect = null) {
    aspect ||= (window.PDD_SIGN_ASPECT || {})[code] || 44 / 82;
    if (code === "8.12") width = 0.95;
    let texture = signTextureCache.get(code);
    if (!texture && window.PDD_SIGN_TEXTURES?.[code]) {
      texture = new THREE.TextureLoader().load(window.PDD_SIGN_TEXTURES[code]);
      texture.anisotropy = Math.min(4, renderer.capabilities.getMaxAnisotropy());
      signTextureCache.set(code, texture);
    }
    const face = new THREE.Mesh(new THREE.PlaneGeometry(width, width / aspect),
      new THREE.MeshBasicMaterial({ map: texture, transparent: true, alphaTest: 0.12 }));
    face.position.z = ROAD_SIGN_FACE_Z;
    face.rotation.y = Math.PI;
    const group = new THREE.Group(); group.add(face);
    addSignBack(face);
    return group;
  }

  function addRoadSign(group, code, z, side = 'right', plate = null, offsetX = 0, speedValue = null, town = null, plateSign = null) {
    const x = (side === 'left' ? 5.4 : -5.4) + offsetX;
    const sign = createRoadSign(code);
    if (town && (code === '5.23.1' || code === '5.24.1')) {
      sign.children.find(o => o.geometry?.type === 'PlaneGeometry').material.map = settlementTexture(code, town);
    }
    if (speedValue !== null && (code === '3.24' || code === '3.25')) {
      // The number is scene data: the bundled generic signs depict 50, while
      // ticket 16.10 specifically shows the end of a 70 km/h restriction.
      const key = code + ':' + speedValue;
      let texture = signTextureCache.get(key);
      if (!texture) {
        const canvas = document.createElement('canvas'); canvas.width = canvas.height = 256;
        const ctx = canvas.getContext('2d'), cancelled = code === '3.25';
        ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(128, 128, 119, 0, Math.PI * 2); ctx.fill();
        ctx.strokeStyle = cancelled ? '#888' : '#cc1725'; ctx.lineWidth = cancelled ? 4 : 20;
        ctx.beginPath(); ctx.arc(128, 128, cancelled ? 117 : 109, 0, Math.PI * 2); ctx.stroke();
        ctx.fillStyle = cancelled ? '#777' : '#151515'; ctx.font = 'bold 128px Arial';
        ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(String(speedValue), 128, 137);
        if (cancelled) {
          ctx.save(); ctx.beginPath(); ctx.arc(128, 128, 116, 0, Math.PI * 2); ctx.clip();
          ctx.strokeStyle = '#444'; ctx.lineWidth = 6;
          for (let d = -28; d <= 28; d += 14) { ctx.beginPath(); ctx.moveTo(30 + d, 230); ctx.lineTo(230 + d, 30); ctx.stroke(); }
          ctx.restore();
        }
        texture = new THREE.CanvasTexture(canvas); signTextureCache.set(key, texture);
      }
      const face = sign.children.find(o => o.geometry?.type === 'PlaneGeometry');
      face.material.map = texture;
      if (face.userData.back) face.userData.back.material = signBackMaterial(texture);
    }
    if (/^1\.4\.\d$/.test(code)) {
      // A standalone approach plate (1.4.2 between the two crossing signs):
      // tall, its own proportions, lower on the post.
      const face = sign.children.find(o => o.geometry?.type === 'PlaneGeometry' && !o.userData.signBack);
      const geometry = new THREE.PlaneGeometry(0.84, 0.84 * 82 / 44);
      face.geometry = geometry; face.position.y = 2.0;
      if (face.userData.back) { face.userData.back.geometry = geometry; face.userData.back.position.y = 2.0; }
    }
    // Larger than junction signs: on a straight the camera sits further back.
    sign.scale.setScalar(code === "6.19.1" ? 2 : 1.25);
    sign.position.set(x, 0, z);
    sign.userData.questionEvidence = true;
    group.add(sign);
    if (plate) { const p = createTextPlate(plate); p.scale.setScalar(1.35); p.position.set(x, 2.15, z); group.add(p); }
    if (plateSign) { const p = createImagePlate(plateSign); p.scale.setScalar(1.35); p.position.set(x, 1.85, z); group.add(p); }
    return sign;
  }
  function addRoadActor(group, cfg, position, yaw, pathPoints, maxSpeed, signalPlan = null) {
    const { actorMesh, halfLength, halfWidth } = createActorMesh(cfg);
    actorMesh.position.copy(position); actorMesh.rotation.y = yaw;
    // Only participants of a question carry a name badge; passing traffic,
    // bus-stop buses, cyclists and the like are just traffic.
    actorMesh.userData.badge.visible = !!cfg.question;
    group.add(actorMesh);
    const path = curve(pathPoints);
    const actor = { mesh: actorMesh, config: cfg, halfLength, halfWidth, initialPos: position.clone(), segment: group,
      path, length: path.getLength(), distance: 0, speed: 0, maxSpeed, clearDistance: Infinity,
      active: false, cleared: false, done: false, gait: 0, waitsForPlayer: true, dependencies: [], road: true,
      signalPlan };
    state.actors.push(actor);
    return actor;
  }

  // Half-width of the asphalt across the corridor at z (0 where no road is
  // built yet): a joining road (junction arm, side street, driveway) shows
  // as asphalt well beyond the street's own width.
  function asphaltHalfAt(z) {
    let h = 0;
    for (let x = 0.5; x <= 18; x += 0.5) {
      if (roadSupports(new THREE.Vector3(x, 0, z)) || roadSupports(new THREE.Vector3(-x, 0, z))) h = x;
      else break;
    }
    return h;
  }
  // The first z (from z0, 5 m steps, at most 80 m on) with the span
  // [z + from, z + to] free of joining roads; null when there is none.
  function clearOfJunctions(z0, [from, to]) {
    refreshRoadBounds();
    const halves = [];
    for (let z = z0 + from - 10; z <= z0 + 80 + to; z += 4) { const h = asphaltHalfAt(z); if (h > 0) halves.push(h); }
    if (!halves.length) return z0;
    const street = Math.min(...halves);
    const joins = z => asphaltHalfAt(z) > street + 1.5;
    for (let z = z0; z <= z0 + 80; z += 5) {
      let clear = true;
      for (let d = from; d <= to && clear; d += 2) clear = !joins(z + d);
      if (clear) return z;
    }
    return null;
  }

  function placeRoadEvent(boundary) {
    if (state.roadEvent) return;
    // Urban road events (a bus bay, crosswalk or a ticket with road markings)
    // start beyond the unpaved stretch, where their paved setting exists.
    if (currentCorridor?.userData.dirtPavedFrom !== undefined) {
      const paved = currentCorridor.localToWorld(new THREE.Vector3(0, 0, currentCorridor.userData.dirtPavedFrom));
      boundary = Math.max(boundary, paved.z - 35);
    }
    const group = new THREE.Group();
    group.userData.roadEvent = true;
    scene.add(group);
    state.roadSegments.push(group);
    state.roadTurn = (state.roadTurn || 0) + 1;
    // A one-way street has no oncoming lane: road questions (overtaking,
    // oncoming traffic, centre lines) and oncoming vehicles do not belong there.
    const oneWay = !!currentCorridor?.userData.oneWay;
    const situation = state.roadTurn % 2 === 1 && !oneWay ? nextRoadSituation() : null;
    const eventKinds = oneWay ? ['busstop', 'crosswalk', 'roadworks', 'obstacle', 'courtyard', 'cyclist']
      : ['busstop', 'crosswalk', 'roadworks', 'obstacle', 'courtyard', 'cyclist', 'emergency'];
    const kind = state.forceRoadEvent || eventKinds[Math.floor(Math.random() * eventKinds.length)];
    if (situation) {
      state.roadEvent = buildQuestionEvent(group, boundary, situation);
    } else if (kind === 'busstop') {
      // The pocket, shelter and merging bus need a straight stretch. At a
      // junction their asphalt used to cover the corner pavement and made a
      // right turn appear to lead onto the sidewalk.
      const z = clearOfJunctions(boundary + 62, [-30, 45]);
      state.roadEvent = z === null ? buildCyclistEvent(group, boundary + 40) : buildBusStopEvent(group, z);
    } else if (kind === 'roadworks' || kind === 'obstacle') {
      // A lane blockage never stands in a junction mouth: step it down the
      // road until nothing joins between its warning and its end.
      const z = clearOfJunctions(boundary + 60, kind === 'roadworks' ? [-20, 22] : [-17, 5]);
      state.roadEvent = z === null ? buildCyclistEvent(group, boundary + 40)
        : kind === 'roadworks' ? buildRoadworksEvent(group, z) : buildObstacleEvent(group, z);
    } else if (kind === 'courtyard') {
      const z = clearOfJunctions(boundary + 60, [-12, 18]);
      state.roadEvent = z === null ? buildCyclistEvent(group, boundary + 40) : buildCourtyardEvent(group, z);
    } else if (kind === 'cyclist') {
      state.roadEvent = buildCyclistEvent(group, boundary + 40);
    } else if (kind === 'emergency') {
      state.roadEvent = buildEmergencyEvent(group, boundary + 60);
    } else {
      const z = clearOfJunctions(boundary + 70, [-12, 12]);
      state.roadEvent = z === null ? buildCyclistEvent(group, boundary + 40) : buildCrosswalkEvent(group, z);
    }
    // Life on the road: oncoming traffic on many stretches, question or not.
    if (!state.forceRoadEvent && !oneWay && !situation?.scene?.wideCity && !situation?.scene?.roadCurve && situation?.scene?.kind !== 'temporary_bypass' && Math.random() < 0.65) addOncomingTraffic(group, boundary, situation ? situation.scene : null);
    trimSegments();
    return state.roadEvent;
  }

  // Road questions own their topology. A nearby random ticket junction must
  // never stand in for the crossing described in a road question.
  // taper: the pavements end on a diagonal (town edge, motorway); a side
  // junction keeps square pavement ends that meet its own corners.
  function replaceCorridorStrip(from, to, build, taper = false) {
    const corridor = state.exitRoad || currentCorridor;
    const environment = new THREE.Group(), pendingTapers = [];
    environment.userData.questionTopology = true;
    if (corridor) {
      scene.updateMatrixWorld(true);
      corridor.traverse(o => {
        if (!o.userData.sceneryObject) return;
        const box = new THREE.Box3().setFromObject(o);
        if (box.max.z >= from && box.min.z <= to) o.visible = false;
      });
      const parts = [];
      corridor.traverse(o => {
        let root = o, scenery = false;
        while (root && root !== corridor) { scenery ||= !!root.userData.sceneryObject; root = root.parent; }
        if (!scenery && (o.isMesh || o.isLine) && !o.userData.actor && o.material) parts.push(o);
      });
      const straightBefore = new THREE.Plane(new THREE.Vector3(0, 0, -1), from);
      const straightAfter = new THREE.Plane(new THREE.Vector3(0, 0, 1), -to);
      // Pavements do not stop square: they taper towards the kerb over 10 m
      // (cut on a diagonal), like a pavement ending at the edge of town.
      const slope = 10 / 3.2;
      // The diagonal never reaches the end of the corridor's pavement: right
      // after a junction it would leave a stub beside the junction corners.
      // Short of room, the pavement runs a little into the strip and narrows
      // there instead.
      let paveStart = Infinity, paveEnd = -Infinity;
      parts.forEach(o => {
        if (o.userData.surface !== 'sidewalk') return;
        const b = new THREE.Box3().setFromObject(o);
        paveStart = Math.min(paveStart, b.min.z); paveEnd = Math.max(paveEnd, b.max.z);
      });
      const taperFrom = Math.max(from, paveStart + 11), taperTo = Math.min(to, paveEnd - 11);
      // The pavement is cut square where the narrowing starts; the narrowing
      // itself is a separate piece whose outer edge eases into the kerb.
      const taperBefore = () => new THREE.Plane(new THREE.Vector3(0, 0, -1), taperFrom);
      const taperAfter = () => new THREE.Plane(new THREE.Vector3(0, 0, 1), -taperTo);
      const taperSides = new Set();
      parts.forEach(o => {
        const box = new THREE.Box3().setFromObject(o);
        if (box.max.z < from || box.min.z > to) return;
        const side = taper && o.userData.surface === 'sidewalk' ? Math.sign(box.getCenter(new THREE.Vector3()).x) : 0;
        if (side) taperSides.add(side);
        // Pavement joint lines stop before the taper starts, so none are left
        // lying on the grass beside a narrowing pavement.
        const lineShift = taper && o.isLine ? 10 : 0;
        // Asphalt runs a SEAM under the new piece: whatever the new piece
        // starts with, no ground shows through at the cut. The textures share
        // their phase, so the overlap itself is invisible.
        const overlap = o.userData.surface === 'road' ? SEAM : 0;
        const before = side ? taperBefore(side) : lineShift ? new THREE.Plane(new THREE.Vector3(0, 0, -1), from - lineShift)
          : overlap ? new THREE.Plane(new THREE.Vector3(0, 0, -1), from + overlap) : straightBefore;
        const after = side ? taperAfter(side) : lineShift ? new THREE.Plane(new THREE.Vector3(0, 0, 1), -(to + lineShift))
          : overlap ? new THREE.Plane(new THREE.Vector3(0, 0, 1), -(to - overlap)) : straightAfter;
        const cloneWithPlanes = (m, planes) => {
          (corridor.userData.replacedMaterials ||= new Set()).add(m);
          const copy = cloneMaterial(m);
          copy.clippingPlanes = [...(m.clippingPlanes || []), ...planes];
          copy.clipShadows = true;
          return copy;
        };
        const mapMaterials = planes => Array.isArray(o.material)
          ? o.material.map(m => cloneWithPlanes(m, planes))
          : cloneWithPlanes(o.material, planes);
        if (box.min.z < from && box.max.z > to) {
          // Only long surfaces such as asphalt and pavement need two halves.
          const copy = o.clone(false);
          const originals = Array.isArray(o.material) ? o.material : [o.material];
          o.material = Array.isArray(o.material)
            ? originals.map(m => cloneWithPlanes(m, [before]))
            : cloneWithPlanes(originals[0], [before]);
          copy.material = Array.isArray(copy.material)
            ? originals.map(m => cloneWithPlanes(m, [after]))
            : cloneWithPlanes(originals[0], [after]);
          o.parent.add(copy);
        } else if (box.min.z < from) {
          o.material = mapMaterials([before]);
        } else if (box.max.z > to) {
          o.material = mapMaterials([after]);
        } else {
          // Scenery wholly inside the replacement is clipped away without
          // creating duplicate buildings, trees or pedestrians.
          o.material = mapMaterials([before, after]);
        }
      });
      const taperLength = slope * 3.2;
      if (taper && taperTo - taperFrom >= 2 * taperLength) for (const side of taperSides)
        for (const [a, b] of [[taperFrom, taperFrom + taperLength], [taperTo - taperLength, taperTo]]) pendingTapers.push({ side, a, b, grow: a !== taperFrom });
      // Ambient walkers must not keep walking through the new carriageway.
      state.ambient = state.ambient.filter(a => {
        const p = a.mesh.getWorldPosition(new THREE.Vector3());
        if (p.z < from - 7 || p.z > to + 7) return true;
        a.mesh.visible = false; return false;
      });
    }
    build(environment);
    // Narrowing pavement pieces: the kerb follows the new piece's asphalt
    // where it swings out (a separate carriageway), never over it.
    if (pendingTapers.length) {
      environment.updateMatrixWorld(true);
      const roads = []; environment.traverse(o => { if (o.isMesh && o.userData.surface === 'road') roads.push(o); });
      const ray = new THREE.Raycaster(), down = new THREE.Vector3(0, -1, 0);
      const onRoad = (x, z) => { ray.set(new THREE.Vector3(x, 5, z), down); return ray.intersectObjects(roads, false).length > 0; };
      for (const { side, a, b, grow } of pendingTapers) {
        const zs = []; for (let q = a; q < b; q += 0.4) zs.push(q); zs.push(b);
        // The new asphalt overlaps the kerb by a SEAM: look 0.15 m beyond it.
        const kerb = new Map(zs.map(q => { let d = 4.2; while (d < 7.4 && onRoad(side * (d + 0.15), q)) d += 0.1; return [q, d]; }));
        const w = q => { const t = THREE.MathUtils.smoothstep(q, a, b); return 3.2 * (grow ? t : 1 - t); };
        const inner = q => kerb.get(q), outer = q => Math.max(inner(q) + 0.02, 4.2 + w(q));
        if (zs.every(q => 4.2 + w(q) <= inner(q) + 0.05)) continue; // the road takes the whole width
        const piece = extrudedStripZ(zs, q => side < 0 ? -outer(q) : inner(q), q => side < 0 ? -inner(q) : outer(q), 0.18,
          new THREE.MeshLambertMaterial({ color: season().sidewalk }));
        piece.userData.surface = 'sidewalk'; piece.material.userData.seasonal = 'sidewalk';
        environment.add(piece);
      }
    }
    scene.add(environment);
    if (corridor) corridor.attach(environment);
    else state.roadSegments.push(environment);
    refreshRoadBounds();
    // Replacement surfaces are created after the corridor has been weathered.
    // Reapply the same wet colour to both sides of every join this frame.
    state.weatherDirty = true;
    applyWeather();
    return environment;
  }

  function roadSurface(group, width, length, x, z, sidewalk = false) {
    const m = new THREE.MeshLambertMaterial({ color: sidewalk ? season().sidewalk : BRAND.asphalt });
    // A pavement strip along the carriageway is exactly 4.2 ... 7.4 across, as
    // every other pavement piece, so its kerb never steps at a join.
    const kerbSide = sidewalk && Math.abs(Math.abs(x) - width / 2 - 4.2) < 0.1;
    const across = kerbSide ? width : width + SEAM;
    if (kerbSide) x = Math.sign(x) * (4.2 + width / 2);
    const surface = addFlatPlane(group, across, length + SEAM, x, z, sidewalk ? 0.18 : 0.02, m);
    surface.userData.surface = sidewalk ? 'sidewalk' : 'road';
    return surface;
  }

  function extendQuestionCorridor(endZ) {
    if (!state.exitRoad || endZ <= nextSegmentZ) return;
    const extra = buildStraightSegment(nextSegmentZ, endZ - nextSegmentZ, true);
    state.exitRoad.attach(extra);
    const ends = corridorWorldEnds();
    const first = Math.min(...ends.map(p => p.z));
    state.exitRoad.userData.roadEnds = [first, endZ].map(z => state.exitRoad.worldToLocal(new THREE.Vector3(0, 0, z)));
    nextSegmentZ = endZ;
  }

  function buildRuralExit(length) {
    const seg=new THREE.Group(),paint=roadMarkingMat();
    const ground=addFlatPlane(seg,44,length+2*SEAM,0,length/2,-.02,new THREE.MeshLambertMaterial({color:season().ground}));ground.material.userData.seasonal='ground';
    roadSurface(seg,8.4,length,0,length/2);
    for(const side of [-1,1]) {
      addFlatPlane(seg,1.3,length,side*4.85,length/2,.015,new THREE.MeshLambertMaterial({color:0xB4AD92}));
      addFlatPlane(seg,.15,length,side*3.95,length/2,.027,paint);
      for(let z=12;z<length;z+=16){const tree=createTree('pine');tree.position.set(side*11,0,z);tree.userData.sceneryObject=true;seg.add(tree);}
    }
    for(let z=2;z<length-2;z+=5)addFlatPlane(seg,.13,2,0,z,.027,paint);
    registerRoadSegment(seg);seg.userData.roadEnds=[new THREE.Vector3(0,0,0),new THREE.Vector3(0,0,length)];return seg;
  }

  function buildRoadQuestionJunction(ev) {
    const j = ev.scene.junction, z = ev.stopZ + j.z, sides=j.noRight?[1]:[-1,1];
    ev.junctionZ = z;
    // Leave room after the authored crossing before the next ticket junction.
    extendQuestionCorridor(z + 55);
    ev.junction = replaceCorridorStrip(z - 9, z + 9, group => {
      roadSurface(group, 8.4, 18, 0, z);
      roadSurface(group,j.noRight?39.2:70,8.4,j.noRight?15.4:0,z);
      if(!j.rural) for (const side of sides) for (const end of [-1, 1]) {
        roadSurface(group, 27.6, 3.2, side * 21.2, z + end * 5.8, true); // corners: addCornerFillet
        roadSurface(group, 3.2, 1.6, side * 5.8, z + end * 8.2, true);
      }
      ev.junctionPreviews = {};
      for (const side of sides) {
        const road = j.rural ? buildRuralExit(200) : buildStraightSegment(0, 200, true, state.district, null, 30);
        road.rotation.y = side * Math.PI / 2;
        road.position.set(side * 35, 0, z);
        group.add(road);
        ev.junctionPreviews[side < 0 ? 'right' : 'left'] = road;
      }
      // Outlives the road event: a turn into a side road must always hand
      // over the corridor, even after the question's stretch has finished.
      state.sideJunction = { junctionZ: z, previews: ev.junctionPreviews, situation: ev.situation, actors: ev.actors };
      const paint = roadMarkingMat();
      for (const side of sides) for (let x = 8; x < 34; x += 5) {
        addFlatPlane(group, 2, 0.13, side * x, z, 0.027, paint);
      }
      // Rounded corners with the edge lines running round them: along the
      // side roads and across the gap in the main road's own edge lines.
      for (const sx of sides) for (const sz of [-1, 1]) {
        addCornerFillet(group, sx, sz, 4.2, 4.2, z, paint);
        addFlatPlane(group, 35 - 7.6, 0.15, sx * (7.6 + 35) / 2, z + sz * 3.95, 0.027, paint);
        addFlatPlane(group, 0.15, 9 - 7.6 + SEAM, sx * 3.95, z + sz * (7.6 + 9) / 2, 0.027, paint);
      }
      if(j.rural) {
        group.children.filter(o=>o.userData.surface==='sidewalk').forEach(o=>{o.visible=false;o.userData.surface='verge';});
        if(j.noRight)addFlatPlane(group,.15,18,-3.95,z,.027,paint);
      }
      if (j.priority === 'secondary') {
        addRoadSign(group, '2.4', z - 7);
      } else if (j.priority === 'stop') {
        addRoadSign(group, '2.5', z - 5.5);
        ev.requiredStopZ = z - 4.2;
      } else if (j.priority === 'main' && j.sideSigns !== false) {
        // Yield signs on the side road also make its priority unambiguous.
        for (const side of sides) {
          const sign = createRoadSign('2.4');
          sign.position.set(side * 8, 0, z + side * 5.4);
          sign.rotation.y = side * Math.PI / 2;
          group.add(sign);
        }
      }
    });
    if (j.priority === 'secondary') {
      ev.laneDeadlineZ = z - 4.2;
      ev.endZ = z + 12;
    }
  }

  // The same strip laid along X (a cross street): z edges as functions of x,
  // split into chunks so drivable bounding boxes stay tight on a taper.
  function addRibbonX(group, from, to, low, high, y, material, chunk = Infinity) {
    const meshes = [];
    for (let a = from; a < to - 1e-6; a = Math.min(to, a + chunk)) {
      const b = Math.min(to, a + chunk), pos = [], idx = [];
      const n = Math.max(1, Math.ceil((b - a) / 0.75));
      for (let i = 0; i <= n; i++) {
        const x = a + (b - a) * i / n;
        pos.push(x, y, low(x), x, y, high(x));
        if (i) idx.push(2 * i - 2, 2 * i, 2 * i - 1, 2 * i - 1, 2 * i, 2 * i + 1);
      }
      const geo = new THREE.BufferGeometry();
      geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3));
      geo.setIndex(idx); geo.computeVertexNormals();
      const mesh = new THREE.Mesh(geo, material);
      material.side = THREE.DoubleSide;
      mesh.receiveShadow = Boolean(material.isMeshLambertMaterial);
      if(material.color?.getHex()===BRAND.asphalt)material.userData.asphalt=true;
      group.add(mesh); meshes.push(mesh);
    }
    return meshes;
  }
  // Pavement along the main street whose x edges follow functions of z.
  function extrudedStripZ(zs, left, right, height, material) {
    const shape = new THREE.Shape();
    shape.moveTo(left(zs[0]), zs[0]);
    zs.forEach(z => shape.lineTo(left(z), z));
    [...zs].reverse().forEach(z => shape.lineTo(right(z), z));
    shape.closePath();
    const geo = new THREE.ExtrudeGeometry(shape, { depth: height, bevelEnabled: false });
    geo.rotateX(Math.PI / 2);
    const mesh = new THREE.Mesh(geo, material);
    mesh.position.y = height; mesh.receiveShadow = true;
    return mesh;
  }
  // A kerb rounded with radius 3.2 m at a junction corner. The square
  // corner of the pavements is left out by the callers and built here: the
  // pavement part up to the curve (a real raised slab, no overlay) and the
  // asphalt part in front of it, which the kerb check treats by the exact
  // curve. The edge line follows the curve and joins both streets' lines.
  function addCornerFillet(group, sx, sz, kerbX, kerbZ, centerZ, paint, r = 3.2, parts = {}) {
    const P = (u, v) => [sx * (kerbX + u), centerZ + sz * (kerbZ + v)];
    const arc = (radius, from, to, n = 16) => Array.from({ length: n + 1 }, (_, i) => {
      const t = from + (to - from) * i / n;
      return [r + radius * Math.cos(t), r + radius * Math.sin(t)];
    });
    const shapeOf = pts => { const sh = new THREE.Shape(); sh.moveTo(...pts[0]); pts.slice(1).forEach(q => sh.lineTo(...q)); sh.closePath(); return sh; };
    // Asphalt: the corner of the square outside the curve.
    const road = shapeOf([[0, 0], ...arc(r, 1.5 * Math.PI, Math.PI)].map(([u, v]) => P(u, v)));
    if (parts.road !== false) {
      const rg = new THREE.ShapeGeometry(road); rg.rotateX(Math.PI / 2);
      const asphalt = new THREE.Mesh(rg, new THREE.MeshLambertMaterial({ color: BRAND.asphalt, side: THREE.DoubleSide }));
      asphalt.position.y = 0.021; asphalt.receiveShadow = true;
      asphalt.userData.surface = 'road';
      asphalt.userData.fillet = { center: new THREE.Vector3(...[P(r, r)].map(([x, z]) => [x, 0, z])[0]), r };
      group.add(asphalt);
    }
    // Pavement: the rest of the square, a slab like the pavements around it.
    const pave = shapeOf([[r, 0], [r, r + 0.02], [0, r + 0.02], ...arc(r, Math.PI, 1.5 * Math.PI)].map(([u, v]) => P(u, v)));
    const pg = new THREE.ExtrudeGeometry(pave, { depth: 0.18, bevelEnabled: false }); pg.rotateX(Math.PI / 2);
    const slabMat = new THREE.MeshLambertMaterial({ color: season().sidewalk, side: THREE.DoubleSide });
    slabMat.userData.seasonal = 'sidewalk';
    const slab = new THREE.Mesh(pg, slabMat);
    slab.position.y = 0.18; slab.receiveShadow = true; slab.userData.surface = 'sidewalk';
    group.add(slab);
    if (parts.line === false) return;
    // Edge line: the arc plus the short pieces up to both straight lines.
    const inner = arc(r + 0.175, 1.5 * Math.PI, Math.PI), outer = arc(r + 0.325, 1.5 * Math.PI, Math.PI);
    inner.unshift([3.4, -0.175]); outer.unshift([3.4, -0.325]);
    inner.push([-0.175, 3.4]); outer.push([-0.325, 3.4]);
    const pos = [], idx = [];
    inner.forEach((q, i) => {
      const [ax, az] = P(...q), [bx, bz] = P(...outer[i]);
      pos.push(ax, 0.032, az, bx, 0.032, bz);
      if (i) idx.push(2 * i - 2, 2 * i, 2 * i - 1, 2 * i - 1, 2 * i, 2 * i + 1);
    });
    const lg = new THREE.BufferGeometry();
    lg.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); lg.setIndex(idx);
    const line = new THREE.Mesh(lg, paint.clone()); line.material.side = THREE.DoubleSide;
    line.userData.roadMarking = true;
    group.add(line);
  }
  // A raised slab (kerbed pavement, median) whose z edges follow functions
  // of x; xs are the sample positions along the street.
  function extrudedStrip(xs, low, high, height, material) {
    const shape = new THREE.Shape();
    shape.moveTo(xs[0], low(xs[0]));
    xs.forEach(x => shape.lineTo(x, low(x)));
    [...xs].reverse().forEach(x => shape.lineTo(x, high(x)));
    shape.closePath();
    const geo = new THREE.ExtrudeGeometry(shape, { depth: height, bevelEnabled: false });
    geo.rotateX(Math.PI / 2);
    const mesh = new THREE.Mesh(geo, material);
    mesh.position.y = height; mesh.castShadow = false; mesh.receiveShadow = true;
    return mesh;
  }

  // A flat strip between two lateral edge functions of z (world X): used for
  // carriageways that swing out or merge smoothly instead of starting square.
  function addRibbon(group, from, to, left, right, y, material, step = 1) {
    const pos = [], idx = [];
    for (let z = from, i = 0; z <= to + 1e-6; z = Math.min(to, z + step), i++) {
      pos.push(left(z), y, z, right(z), y, z);
      if (i) idx.push(2 * i - 2, 2 * i, 2 * i - 1, 2 * i - 1, 2 * i, 2 * i + 1);
      if (z === to) break;
    }
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3));
    geo.setIndex(idx); geo.computeVertexNormals();
    const mesh = new THREE.Mesh(geo, material);
    mesh.material.side = THREE.DoubleSide;
    mesh.receiveShadow = Boolean(material.isMeshLambertMaterial);
    if(material.color?.getHex()===BRAND.asphalt)material.userData.asphalt=true;
    group.add(mesh);
    return mesh;
  }

  // Edge line 1.2 a quarter metre inside a kerb that runs along Z; kerb(q)
  // is the kerb's world X, side the side of the road it is on (+1 / -1).
  function addEdgeLineZ(group, from, to, kerb, side, paint = roadMarkingMat()) {
    if (to - from < 0.3) return null;
    const x = q => kerb(q) - side * 0.25;
    const line = addRibbon(group, from, to, q => x(q) - 0.075, q => x(q) + 0.075, 0.027, paint, 0.5);
    line.userData.roadMarking = true;
    return line;
  }
  // Flat quads with world (baked) corners: [[ax,az],[bx,bz],[cx,cz],[dx,dz]].
  function addBakedQuads(group, quads, y, material) {
    const pos = [], idx = [];
    quads.forEach((q, i) => {
      q.forEach(([x, z]) => pos.push(x, y, z));
      idx.push(4 * i, 4 * i + 1, 4 * i + 2, 4 * i, 4 * i + 2, 4 * i + 3);
    });
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3));
    geo.setIndex(idx); geo.computeVertexNormals();
    material.side = THREE.DoubleSide;
    const mesh = new THREE.Mesh(geo, material);
    mesh.receiveShadow = Boolean(material.isMeshLambertMaterial);
    group.add(mesh);
    return mesh;
  }
  // A kerbed island with round ends (a stadium) from x0 to x1 along X,
  // `half` wide either side of z = 0; lawn on top. Coordinates are world X
  // and Z from `centerZ` (baked, like extrudedStrip).
  function addRoundIsland(group, x0, x1, half, centerZ, zOffset = 0) {
    const a = Math.min(x0, x1) + half, b = Math.max(x0, x1) - half;
    const stadium = h => {
      const sh = new THREE.Shape();
      sh.moveTo(a, zOffset - h); sh.lineTo(b, zOffset - h);
      sh.absarc(b, zOffset, h, -Math.PI / 2, Math.PI / 2, false);
      sh.lineTo(a, zOffset + h);
      sh.absarc(a, zOffset, h, Math.PI / 2, Math.PI * 1.5, false);
      return sh;
    };
    const geo = new THREE.ExtrudeGeometry(stadium(half), { depth: 0.18, bevelEnabled: false, curveSegments: 14 });
    geo.rotateX(Math.PI / 2);
    const kerb = new THREE.Mesh(geo, new THREE.MeshLambertMaterial({ color: BRAND.sidewalk }));
    kerb.position.set(0, 0.18, centerZ); kerb.receiveShadow = true; kerb.userData.surface = 'sidewalk';
    kerb.userData.noRoad = p => { const x = THREE.MathUtils.clamp(p.x, a, b); return Math.hypot(p.x - x, p.z - zOffset) < half - 0.05; };
    group.add(kerb);
    const lawnMat = new THREE.MeshLambertMaterial({ color: season().ground, side: THREE.DoubleSide }); lawnMat.userData.seasonal = 'ground';
    const lawnGeo = new THREE.ShapeGeometry(stadium(Math.max(0.05, half - 0.16)), 14); lawnGeo.rotateX(Math.PI / 2);
    const lawn = new THREE.Mesh(lawnGeo, lawnMat); lawn.position.set(0, 0.186, centerZ); group.add(lawn);
    return kerb;
  }

  // Motorway (5.1 ... 5.2): the oncoming lane swings out into a separate
  // carriageway behind a grass median over 45 m and merges back the same way
  // at the end — no second road appearing out of nowhere. The player's own
  // carriageway keeps both lanes in its direction.
  function buildQuestionMotorway(ev) {
    ev.motorwayFrom = ev.stopZ + 4; ev.motorwayTo = ev.stopZ + 175; ev.endZ = ev.motorwayTo;
    ev.motorway = replaceCorridorStrip(ev.motorwayFrom, ev.motorwayTo, group => {
      const from = ev.motorwayFrom, to = ev.motorwayTo, taper = 45;
      const length = to - from, mid = (to + from) / 2;
      // 0 at both ends, 1 on the separated stretch.
      const k = z => THREE.MathUtils.smoothstep(z, from, from + taper) * (1 - THREE.MathUtils.smoothstep(z, to - taper, to));
      const inner = z => 7.2 * k(z);                                     // 0 -> 7.2
      const outer = z => 4.2 + 11.4 * k(z);                              // 4.2 -> 15.6
      roadSurface(group, 8.4, length, 0, mid);
      const asphalt = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
      // The opposite carriageway can be driven onto (it is a violation, and
      // the merge at the end brings the car back): short chunks keep each
      // drivable bounding box off the median.
      for (let z = from; z < to - 1e-6; z += 2) {
        const m = addRibbon(group, z, Math.min(to, z + 2), inner, outer, 0.021, asphalt, 0.5);
        m.userData.surface = 'road'; m.userData.oppositeCarriageway = true;
      }
      const grass = new THREE.MeshLambertMaterial({ color: season().ground });
      grass.userData.seasonal = 'ground';
      const median = addRibbon(group, from, to, () => 4.2, z => Math.max(4.2, inner(z)), 0.024, grass);
      median.userData.surface = 'median';
      const paint = roadMarkingMat(), dashes = [];
      // Own carriageway: lane divider and both edge lines (the left one only
      // where the median exists).
      for (let p = from + 2; p < to - 2; p += 5) dashes.push(addFlatPlane(new THREE.Group(), 0.13, 2, 0, p, 0.028, paint));
      addFlatPlane(group, 0.15, length, -3.95, mid, 0.028, paint);
      const split = taper * 0.6; // the carriageways are apart from here on
      addRibbon(group, from + split, to - split, () => 3.88, () => 4.02, 0.029, paint);
      // Opposite carriageway: its edges and lane divider follow the swing.
      addRibbon(group, from + split, to - split, z => inner(z) + 0.18, z => inner(z) + 0.32, 0.029, paint);
      addRibbon(group, from, to, z => outer(z) - 0.32, z => outer(z) - 0.18, 0.029, paint);
      for (let p = from + split; p < to - split - 2; p += 5) {
        const c = (inner(p + 1) + outer(p + 1)) / 2;
        const d = addFlatPlane(new THREE.Group(), 0.13, 2, c, p + 1, 0.029, paint);
        dashes.push(d);
      }
      group.add(mergeStatic(dashes, paint));
    }, true);
  }

  // A railway crossing across the question's road (tickets 2.16, 10.11,
  // 17.11, 21.11): a single track on a concrete deck, the track bed running
  // off both ways, a signal with sign 1.3.1 facing each direction (flashing
  // white-moon = open, alternating red = closed) and, with a barrier, a boom
  // over the right half of each approach.
  function buildRailwayCrossing(ev) {
    const r = ev.scene.railway, cz = ev.stopZ + r.z;
    ev.crossingZ = cz;
    extendQuestionCorridor(cz + 60);
    const closed = r.closed ?? (!!r.barrier && !r.barrierOpen);
    const rail = ev.rail = { open: !closed, signalsUnlit: r.signalsUnlit === true, whiteSignal: r.whiteSignal !== false, crossbuck: r.crossbuck !== false, lift: r.barrier && !r.barrierOpen ? 0 : 1, booms: [], red: [], white: [], train: null };
    let hadPavement = false;
    {
      const corridor = state.exitRoad || currentCorridor, lastZ = cz + 6 + ((r.tracks || 1) - 1) * 5;
      if (corridor) {
        scene.updateMatrixWorld(true);
        corridor.traverse(o => {
          if (hadPavement || o.userData.surface !== 'sidewalk' || !o.visible) return;
          const b = new THREE.Box3().setFromObject(o), c = b.getCenter(new THREE.Vector3());
          // A pavement already cut away here (a rural stretch replaced the
          // town street) is not a pavement to continue across the tracks.
          const at = new THREE.Vector3(c.x, 0.18, THREE.MathUtils.clamp(cz, b.min.z, b.max.z));
          let shown = true; for (let p = o; p; p = p.parent) shown &&= p.visible;
          if (shown && !clippedAway(o.material, at) && b.max.z >= cz - 6 && b.min.z <= lastZ && Math.abs(c.x) > 3) hadPavement = true;
        });
      }
    }
    ev.railway = replaceCorridorStrip(cz - 6, cz + 6 + ((r.tracks || 1) - 1) * 5, g => {
      roadSurface(g, 8.4, 12 + ((r.tracks || 1) - 1) * 5, 0, cz + ((r.tracks || 1) - 1) * 2.5);
      const paint = roadMarkingMat();
      const tracks = Array.from({length:r.tracks || 1}, (_, i) => i * 5);
      for (const x of [-3.95, 3.95]) for (const end of [-1, 1]) addFlatPlane(g, 0.15, 4, x, cz + end * 4, 0.027, paint);
      for (const dz of tracks) addFlatPlane(g, 8.4, 3.8, 0, cz + dz, 0.03, new THREE.MeshLambertMaterial({ color: 0x9C9B94 })).userData.roadDeck = true; // deck panels
      // Ballast: a low bed up to the sleepers' sides, sloping to the ground,
      // over the same 72 m x 3.6 m footprint as the former flat strip.
      const ballast = new THREE.MeshLambertMaterial({ color: 0x8C867C });
      const bed = new THREE.Shape([[-1.8, 0], [-1.32, 0.1], [1.32, 0.1], [1.8, 0]].map(([x, y]) => new THREE.Vector2(x, y)));
      for (const dz of tracks) for (const side of [-1, 1]) {
        const geo = new THREE.ExtrudeGeometry(bed, { depth: 72, bevelEnabled: false }); geo.rotateY(Math.PI / 2);
        const mesh = new THREE.Mesh(geo, ballast);
        mesh.position.set(side > 0 ? 4.2 : -76.2, 0, cz + dz); mesh.receiveShadow = true; mesh.userData.ballast = true; g.add(mesh);
      }
      const sleeperMat = new THREE.MeshLambertMaterial({ color: 0x5E4B3B }), sleepers = [];
      for (let x = -75; x <= 75; x += 0.8) {
        if (Math.abs(x) < 4.6) continue;
        const sleeper = new THREE.Mesh(new THREE.BoxGeometry(0.26, 0.1, 2.6), sleeperMat);
        for (const dz of tracks) { const part = sleeper.clone(); part.position.set(x, 0.09, cz + dz); sleepers.push(part); }
      }
      const sleeperMesh = mergeStatic(sleepers, sleeperMat); sleeperMesh.userData.sleepers = true; g.add(sleeperMesh);
      // Rails keep their former box (0.13 m wide, 0.1 m high, same heights):
      // a bright worn head on a darker web and foot.
      const railHead = new THREE.MeshLambertMaterial({ color: 0xD6DCE0 }), railBody = new THREE.MeshLambertMaterial({ color: 0x6F675F });
      const heads = [], bodies = [];
      for (const track of tracks) for (const dz of [track - 0.76, track + 0.76]) {
        for(const [from,to,y] of [[-75,-4.2,.185],[-4.2,4.2,.09],[4.2,75,.185]]) {
          const part = (h, w, yc, list) => { const m = new THREE.Mesh(new THREE.BoxGeometry(to - from, h, w)); m.position.set((from + to) / 2, yc, cz + dz); list.push(m); };
          part(.025, .13, y - .0375, bodies); part(.04, .036, y - .005, bodies); part(.035, .072, y + .0325, heads);
        }
      }
      for (const [parts, mat] of [[heads, railHead], [bodies, railBody]]) {
        const rails = mergeStatic(parts, mat); rails.userData.crossingRail = true; g.add(rails);
        parts.forEach(m => m.geometry.dispose());
      }
      // Pavements run on at full width, exactly as before the crossing. Only
      // two thin gaps are left at each rail so the rails pass across the pavement.
      const stripFrom = cz - 6, stripTo = cz + 6 + (tracks.length - 1) * 5;
      const gaps = [];
      for (const track of tracks) for (const dz of [track - 0.76, track + 0.76]) gaps.push([cz + dz - 0.08, cz + dz + 0.08]);
      gaps.sort((a, b) => a[0] - b[0]);
      let cursor = stripFrom;
      const pieces = [];
      for (const [a, b] of gaps) { if (a > cursor) pieces.push([cursor, a]); cursor = b; }
      if (stripTo > cursor) pieces.push([cursor, stripTo]);
      if (hadPavement) for (const side of [-1, 1]) for (const [a, b] of pieces) roadSurface(g, 3.2, b-a-SEAM, side*5.8, (a+b)/2, true);
      // One signal per direction, on the right of its approach, 1.3.1 below
      // the lamps; the opposite one is the same turned round.
      for (const dir of [1, -1]) {
        const post = r.signals === false ? createRoadSign(r.tracks > 1 ? '1.3.2' : '1.3.1') : createRailwaySignal(rail);
        post.position.set(-dir * 5.2, 0, cz - dir * 4.6);
        post.rotation.y = dir > 0 ? 0 : Math.PI;
        post.userData.questionEvidence = true;
        g.add(post);
        if (r.barrier) {
          const boom = createBarrierBoom();
          boom.position.set(-dir * 4.75, 0, cz - dir * 7);
          boom.rotation.y = dir > 0 ? 0 : Math.PI;
          g.add(boom); rail.booms.push(boom);
        }
      }
    }, false);
    setRailwayBooms(rail);
    ev.barrierZ = r.barrier ? cz - 7 : null;
    ev.railBoundaryZ = cz - (r.stopOffset ?? (r.barrier ? 7 : 4.6));
    updateRailwaySignals(rail);
  }

  // Railway signal: post, a black plate with two red lamps side by side and
  // the white-moon lamp above, sign 1.3.1 under them. Faces -Z (the traffic
  // it serves comes up the road towards it).
  function createRailwaySignal(rail) {
    const g = new THREE.Group();
    const metal = new THREE.MeshLambertMaterial({ color: 0xE9ECEE }), black = new THREE.MeshLambertMaterial({ color: 0x15181B });
    const post = new THREE.Mesh(new THREE.CylinderGeometry(0.07, 0.08, 4.1, 8), metal);
    post.position.y = 2.05; post.castShadow = true; g.add(post);
    // Black and white bands at the foot of the post.
    for (let y = 0.2; y < 1.4; y += 0.5) { const band = new THREE.Mesh(new THREE.CylinderGeometry(0.085, 0.085, 0.25, 8), black); band.position.y = y; g.add(band); }
    const plate = new THREE.Mesh(new THREE.BoxGeometry(1.2, 0.5, 0.08), black);
    plate.position.set(0, 3.45, -0.12); g.add(plate);
    const lampGeo = new THREE.CylinderGeometry(0.17, 0.17, 0.06, 18).rotateX(Math.PI / 2);
    [-0.36, 0.36].forEach(x => {
      const lamp = new THREE.Mesh(lampGeo, new THREE.MeshBasicMaterial({ color: 0x3A1414 }));
      lamp.position.set(x, 3.45, -0.18); g.add(lamp);
      const glow = window.PDD_VEHICLES.addGlow(lamp, 0xFF3434, 1.3); glow.position.z = -0.08; glow.visible = false;
      rail.red.push({ lamp, glow });
    });
    if (rail.whiteSignal) {
    const white = new THREE.Mesh(lampGeo, new THREE.MeshBasicMaterial({ color: 0x3C3E44 }));
    white.position.set(0, 3.95, -0.14); g.add(white);
    const hood = new THREE.Mesh(new THREE.BoxGeometry(0.44, 0.44, 0.08), black); hood.position.set(0, 3.95, -0.09); g.add(hood);
    const whiteGlow = window.PDD_VEHICLES.addGlow(white, 0xEAF2FF, 1.1); whiteGlow.position.z = -0.08; whiteGlow.visible = false;
    rail.white.push({ lamp: white, glow: whiteGlow });
    }
    if (rail.crossbuck) {
    const cross = createRoadSign('1.3.1', 4.4);
    cross.children.filter(o => o.geometry?.type === 'CylinderGeometry').forEach(o => { o.visible = false; });
    cross.scale.setScalar(0.55); cross.position.z = -0.1;
    g.add(cross);
    }
    return g;
  }

  // A barrier boom hinged at a post on the right-hand kerb, reaching across
  // the right half of the road (+X from the hinge), red and white stripes.
  function createBarrierBoom() {
    const g = new THREE.Group();
    const post = new THREE.Mesh(new THREE.BoxGeometry(0.34, 1.1, 0.34), new THREE.MeshLambertMaterial({ color: 0xD8DDE0 }));
    post.position.y = 0.55; post.castShadow = true; g.add(post);
    const canvas = document.createElement('canvas'); canvas.width = 256; canvas.height = 16;
    const ctx = canvas.getContext('2d');
    for (let i = 0; i < 8; i++) { ctx.fillStyle = i % 2 ? '#F4F4F4' : '#D42A22'; ctx.fillRect(i * 32, 0, 32, 16); }
    const arm = new THREE.Group(); arm.position.set(0, 1.0, 0); g.add(arm);
    const boom = new THREE.Mesh(new THREE.BoxGeometry(4.3, 0.12, 0.12),
      new THREE.MeshLambertMaterial({ map: new THREE.CanvasTexture(canvas) }));
    boom.position.x = 2.3; boom.castShadow = true; arm.add(boom);
    g.userData.arm = arm;
    return g;
  }

  function setRailwayBooms(rail) {
    // Raised booms stand almost upright (as in the photo of 2.16).
    rail.booms.forEach(b => { b.userData.arm.rotation.z = rail.lift * Math.PI * 0.47; });
  }

  // Closed: the two red lamps alternate; open: the white-moon lamp flashes.
  function updateRailwaySignals(rail) {
    const t = state.signalClock || 0, phase = Math.floor(t / 0.5) % 2;
    rail.red.forEach(({ lamp, glow }, i) => {
      const on = !rail.signalsUnlit && !rail.open && phase === i % 2;
      lamp.material.color.setHex(on ? 0xFF3434 : 0x3A1414); glow.visible = on;
    });
    rail.white.forEach(({ lamp, glow }) => {
      const on = !rail.signalsUnlit && rail.open && Math.floor(t / 0.7) % 2 === 0;
      lamp.material.color.setHex(on ? 0xEAF2FF : 0x3C3E44); glow.visible = on;
    });
  }

  // A stop is counted only with the nose immediately BEFORE its actual boundary.
  // The automatic question pause may be far earlier and must not satisfy it.
  function checkRequiredStop(owner, boundary, dt, report) {
    const front = playerCarGroup.position.z + Math.cos(playerCarGroup.rotation.y) * playerCarGroup.userData.halfLength;
    if (Math.cos(playerCarGroup.rotation.y) < 0.5 || owner.stopSatisfied) return;
    if (front <= boundary + 0.15 && front >= boundary - 1.8 && Math.abs(state.speed) < 0.25) {
      owner.stopWait = (owner.stopWait || 0) + dt;
      if (owner.stopWait >= 0.6) owner.stopSatisfied = true;
    } else owner.stopWait = 0;
    if (front > boundary + 0.25 && !owner.stopSatisfied && !owner.stopPenalized) {
      owner.stopPenalized = true; report('stop');
    }
  }

  // Authored junction outlines and exit bearings share one physical footprint.
  // Coordinates here are world X/Z; unlike object positions, baked geometry
  // isn't mirrored by registerRoadSegment.
  function polygonContains(outline,x,z) {
    let inside=false;
    for(let i=0,j=outline.length-1;i<outline.length;j=i++) {
      const [xi,zi]=outline[i],[xj,zj]=outline[j];
      if((zi>z)!==(zj>z) && x<(xj-xi)*(z-zi)/(zj-zi)+xi)inside=!inside;
    }
    return inside;
  }
  function polygonShape(outline) {
    const sh=new THREE.Shape();outline.forEach(([x,z],i)=>i?sh.lineTo(x,-z):sh.moveTo(x,-z));sh.closePath();return sh;
  }
  function offsetOutline(outline,width) {
    let area=0;outline.forEach(([x,z],i)=>{const b=outline[(i+1)%outline.length];area+=x*b[1]-b[0]*z;});
    const orientation=Math.sign(area);
    return outline.map((p,i)=>{
      const a=outline[(i+outline.length-1)%outline.length],b=outline[(i+1)%outline.length];
      const normal=(a,b)=>{const dx=b[0]-a[0],dz=b[1]-a[1],len=Math.hypot(dx,dz);return [orientation*dz/len,-orientation*dx/len];};
      const u=normal(a,p),v=normal(p,b),k=Math.min(7,width/Math.max(.2,1+u[0]*v[0]+u[1]*v[1]));
      return [p[0]+(u[0]+v[0])*k,p[1]+(u[1]+v[1])*k];
    });
  }
  function clearJunctionFabric(seg) {
    for(const child of [...seg.children])if(!child.userData.editKey&&!child.userData.trajectoryLabel) {
      seg.remove(child);child.traverse(o=>{o.geometry?.dispose();if(o.material&&!Array.isArray(o.material))o.material.dispose();});
      state.occluders=state.occluders.filter(o=>o!==child);
    }
  }
  function buildAuthoredJunctionFabric(seg,z,situation) {
    clearJunctionFabric(seg);
    const layout=situation.junctionLayout,outline=layout.outline,outer=offsetOutline(outline,3.2);
    const lawn=Math.min((state.district+1)%DISTRICTS,2);
    const ground=addFlatPlane(seg,70,60,0,z,-.02,new THREE.MeshLambertMaterial({color:season().verge[lawn]}));
    ground.material.userData.seasonal='verge'+lawn;
    const geo=new THREE.ShapeGeometry(polygonShape(outline));geo.rotateX(-Math.PI/2);
    const road=new THREE.Mesh(geo,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));road.position.set(0,.02,z);road.receiveShadow=true;
    road.userData.surface='road';road.userData.containsRoad=p=>polygonContains(outline,p.x,p.z);seg.add(road);
    // An offset ring gives every angled arm a full-width pavement. Clip its
    // end caps at the road mouths so it joins the straight previews exactly.
    const shape=polygonShape(outer),hole=polygonShape(outline);shape.holes.push(hole);
    const pavementGeo=new THREE.ExtrudeGeometry(shape,{depth:.18,bevelEnabled:false});pavementGeo.rotateX(-Math.PI/2);
    const mouths=[...layout.arms,{x:0,z:-26,yaw:Math.PI}];
    const caps=mouths.map(a=>{const f=new THREE.Vector3(Math.sin(a.yaw),0,Math.cos(a.yaw));return new THREE.Plane(f.clone().negate(),a.x*f.x+(z+a.z)*f.z);});
    const material=new THREE.MeshLambertMaterial({color:BRAND.sidewalk,clippingPlanes:caps});
    const sw=new THREE.Mesh(pavementGeo,material);sw.position.z=z;sw.userData.surface='sidewalk';sw.receiveShadow=true;
    sw.userData.noRoad=p=>polygonContains(outer,p.x,p.z)&&!polygonContains(outline,p.x,p.z);seg.add(sw);
    const paint=roadMarkingMat();
    // A mouth edge lies across an arm's end; every other outline edge is a
    // kerb and gets the edge line 0.25 m inside it, mitred at the corners.
    const onMouthOf=(a,[x,q])=>Math.abs((x-a.x)*Math.sin(a.yaw)+(q-a.z)*Math.cos(a.yaw))<.05&&Math.abs((x-a.x)*Math.cos(a.yaw)-(q-a.z)*Math.sin(a.yaw))<4.3;
    let area=0;outline.forEach(([x,q],i)=>{const b=outline[(i+1)%outline.length];area+=x*b[1]-b[0]*q;});
    const orient=Math.sign(area),count=outline.length,quads=[],edges=[];
    for(let i=0;i<count;i++){const a=outline[i],b=outline[(i+1)%count];edges.push({a,b,mouth:mouths.some(m=>onMouthOf(m,a)&&onMouthOf(m,b))});}
    const inward=e=>{const dx=e.b[0]-e.a[0],dq=e.b[1]-e.a[1],l=Math.hypot(dx,dq);return [-orient*dq/l,orient*dx/l];};
    const corner=(prev,next,p,w)=>{
      // Mitred with a kerb neighbour; at a mouth, square and a SEAM past it.
      const v=inward(next),u=inward(prev);
      if(prev.mouth||next.mouth){const e=prev.mouth?next:prev,n=inward(e),dx=e.b[0]-e.a[0],dq=e.b[1]-e.a[1],l=Math.hypot(dx,dq),t=prev.mouth?-SEAM:SEAM;
        return [p[0]+n[0]*w+dx/l*t,p[1]+n[1]*w+dq/l*t];}
      const k=w/Math.max(.2,1+u[0]*v[0]+u[1]*v[1]);return [p[0]+(u[0]+v[0])*k,p[1]+(u[1]+v[1])*k];
    };
    edges.forEach((e,i)=>{
      if(e.mouth)return;
      const prev=edges[(i+count-1)%count],next=edges[(i+1)%count];
      const a1=corner(prev,e,e.a,.175),a2=corner(prev,e,e.a,.325),b1=corner(e,next,e.b,.175),b2=corner(e,next,e.b,.325);
      quads.push([a1,b1,b2,a2].map(([x,q])=>[x,z+q]));
    });
    addBakedQuads(seg,quads,.03,paint).userData.roadMarking=true;
    // Each mouth overlaps the road it joins by a SEAM: no seam of ground shows.
    const patches=mouths.map(a=>{const f=[Math.sin(a.yaw),Math.cos(a.yaw)],n=[f[1],-f[0]];
      return [[-1,-1],[1,-1],[1,1],[-1,1]].map(([s,t])=>[a.x+n[0]*4.2*s+f[0]*SEAM*t,z+a.z+n[1]*4.2*s+f[1]*SEAM*t]);});
    addBakedQuads(seg,patches,.02,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));
    for(const arm of mouths) {
      const length=Math.hypot(arm.x,arm.z),f=new THREE.Vector3(Math.sin(arm.yaw),0,Math.cos(arm.yaw));
      for(let d=11;d<length;d+=5) {
        const at=f.clone().multiplyScalar(Math.min(d+1,length-1));
        // Factory object positions are mirrored later; rotations likewise.
        const mark=addFlatPlane(seg,.13,Math.min(2,length-d),-at.x,z+at.z,.03,paint);mark.rotation.z=arm.yaw;
      }
    }
    for(const [x,q] of [[-12,-13],[12,-15],[18,14],[-29,6]]) {
      const tree=createTree('round');tree.position.set(-x,0,z+q);seg.add(tree);
    }
  }

  function buildSpecialMainFabric(seg,z,situation) {
    clearJunctionFabric(seg);
    const motorway=situation.geometry==='motorway_parallel',offset=situation.offsetTramRoad?-4.2:0;
    const width=motorway?29.2:16.8;
    if(situation.offsetTramRoad)replaceCorridorStrip(z-60,z-26,g=>{
      const k=q=>THREE.MathUtils.smoothstep(q,z-60,z-36),low=q=>-4.2-8.4*k(q),high=()=>4.2;
      const road=addRibbon(g,z-60-SEAM,z-26+SEAM,low,high,.02,new THREE.MeshLambertMaterial({color:BRAND.asphalt}),.5);
      road.userData.surface='road';road.userData.containsRoad=p=>p.x>=low(p.z)&&p.x<=4.2;
      const zs=[];for(let q=z-60;q<=z-26;q+=.5)zs.push(q);
      for(const side of [-1,1]){const edge=side<0?low:high;const sw=extrudedStripZ(zs,q=>edge(q)+(side<0?-3.2:0),q=>edge(q)+(side>0?3.2:0),.18,new THREE.MeshLambertMaterial({color:season().sidewalk}));sw.userData.surface='sidewalk';g.add(sw);}
      const paint=roadMarkingMat();for(let q=z-59;q<z-27;q+=5){addFlatPlane(g,.13,2,0,q,.028,paint);addFlatPlane(g,.13,2,-3.6*k(q),q,.028,paint);}
      addEdgeLineZ(g,z-60-SEAM,z-26+SEAM,low,-1,paint);addEdgeLineZ(g,z-60-SEAM,z-26+SEAM,high,1,paint);
    });

    const k=q=>situation.offsetTramRoad&&q<z?1:1-THREE.MathUtils.smoothstep(Math.abs(q-z),13,25);
    const low=q=>-4.2+(offset-width/2+4.2)*k(q),high=q=>4.2+(offset+width/2-4.2)*k(q);
    const asphalt=new THREE.MeshLambertMaterial({color:BRAND.asphalt}),paint=roadMarkingMat();
    const ground=addFlatPlane(seg,76,60,0,z,-.02,new THREE.MeshLambertMaterial({color:season().ground}));ground.material.userData.seasonal='ground';
    const road=addRibbon(seg,z-26-SEAM,z+26+SEAM,low,high,.02,asphalt,.5);road.userData.surface='road';
    road.userData.containsRoad=p=>p.x>=low(p.z)&&p.x<=high(p.z);
    if(!motorway)roadSurface(seg,70,8.4,0,z);
    for(const side of [-1,1]) {
      const edge=side<0?low:high;
      const spans=motorway?[[z-26,z+26]]:[[z-26,z-7.4],[z+7.4,z+26]];
      for(const [a,b] of spans) {
        const zs=[];for(let q=a;q<b;q+=.5)zs.push(q);zs.push(b);
        const slab=extrudedStripZ(zs,q=>edge(q)+(side<0?-3.2:0),q=>edge(q)+(side>0?3.2:0),motorway?.015:.18,new THREE.MeshLambertMaterial({color:motorway?0xB4AD92:season().sidewalk}));
        if(!motorway)slab.userData.surface='sidewalk';seg.add(slab);
      }
      if(!motorway)for(const end of [-1,1]) {
        const kerb=side<0?12.6:4.2;
        addCornerFillet(seg,side,end,kerb,4.2,z,paint);
        const from=kerb+3.2,length=35-from;
        pavementRect(seg,length,3.2,-side*(35+from)/2,z+end*5.8);
      }
    }
    for(const side of [-1,1]) {
      const edge=side<0?low:high;
      if(motorway)addEdgeLineZ(seg,z-26-SEAM,z+26+SEAM,edge,side,paint);
      else {addEdgeLineZ(seg,z-26-SEAM,z-7.6,edge,side,paint);addEdgeLineZ(seg,z+7.6,z+26+SEAM,edge,side,paint);}
    }
    const dividerXs=motorway?[-10.4,-6.2,6.2,10.4]:[0,-3.6];
    for(const x of dividerXs)for(let q=z-25;q<z+25;q+=5) {
      if(!motorway && Math.abs(q-z)<4.2)continue;
      const mark=addFlatPlane(seg,.13,2,-x*k(q),q,.028,paint);mark.userData.roadMarking=true;
    }
    if(motorway) {
      const half=q=>2*k(q),zs=[];for(let q=z-26;q<z+26;q+=.5)zs.push(q);zs.push(z+26);
      const median=extrudedStripZ(zs,q=>-half(q),half,.18,new THREE.MeshLambertMaterial({color:BRAND.sidewalk}));
      median.userData.noRoad=p=>p.z>=z-26&&p.z<=z+26&&Math.abs(p.x)<half(p.z)-.05;seg.add(median);
      const turf=new THREE.MeshLambertMaterial({color:season().ground});turf.userData.seasonal='ground';
      addRibbon(seg,z-26,z+26,q=>-Math.max(0,half(q)-.12),q=>Math.max(0,half(q)-.12),.186,turf,.5);
      for(const side of [-1,1])for(let q=z-24;q<z+24;q+=12){const tree=createTree('pine');tree.position.set(-side*(width/2+7),0,q);seg.add(tree);}
    }
  }

  function buildCourtyardQuestionFabric(seg, start, z, situation) {
    // Replace the four-arm scaffold with one driveway through a building.
    for (const child of [...seg.children]) {
      if (!child.userData.editKey && !child.userData.trajectoryLabel) {
        seg.remove(child); child.traverse(o => { o.geometry?.dispose(); if(o.material && !Array.isArray(o.material)) o.material.dispose(); });
      }
    }
    const sides = situation.geometry === 'courtyard_both' ? [-1,1] : [situation.geometry.endsWith('left') ? -1 : 1];
    const drivewayWidth = situation.geometry === 'courtyard_both' ? 5.2 : 8.4;
    const width=situation.mainWidth||8.4,kerb=width/2;
    const half=q=>4.2+(kerb-4.2)*(1-THREE.MathUtils.smoothstep(Math.abs(q-z),13,25));
    const road=addRibbon(seg,start-SEAM,start+52+SEAM,q=>-half(q),half,.02,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));road.userData.surface='road';
    road.userData.containsRoad=p=>p.x>=-half(p.z)&&p.x<=half(p.z);
    const paint = roadMarkingMat();
    for (const side of [-1,1]) {
      if (sides.includes(side)) {
        for (const end of [-1,1]) {
          const from=drivewayWidth/2+3.2;
          const a=end<0?z-26:z+from,b=end<0?z-from:z+26,zs=[];for(let q=a;q<b;q+=.5)zs.push(q);zs.push(b);
          const slab=extrudedStripZ(zs,q=>side<0?half(q):-half(q)-3.2,q=>side<0?half(q)+3.2:-half(q),.18,new THREE.MeshLambertMaterial({color:season().sidewalk}));slab.userData.surface='sidewalk';seg.add(slab);
          addCornerFillet(seg,-side,end,kerb,drivewayWidth/2,z,paint);
        }
        addCourtyardGateway(seg,side,z,drivewayWidth,situation.openEntrance===true,situation.clearYard===true);
      } else {
        const zs=[];for(let q=z-26;q<z+26;q+=.5)zs.push(q);zs.push(z+26);
        const slab=extrudedStripZ(zs,q=>side<0?half(q):-half(q)-3.2,q=>side<0?half(q)+3.2:-half(q),.18,new THREE.MeshLambertMaterial({color:season().sidewalk}));slab.userData.surface='sidewalk';seg.add(slab);
      }
    }
    // Edge lines along both kerbs; on a driveway's side they stop where the
    // rounded corner's own line takes over.
    for (const side of [-1,1]) {
      const kerbAt=q=>side<0?half(q):-half(q),from=start-SEAM,to=start+52+SEAM,gap=drivewayWidth/2+3.4;
      if (sides.includes(side)) { addEdgeLineZ(seg,from,z-gap,kerbAt,-side,paint); addEdgeLineZ(seg,z+gap,to,kerbAt,-side,paint); }
      else addEdgeLineZ(seg,from,to,kerbAt,-side,paint);
    }
    if (!situation.unmarkedCentre) for (let q=start+1;q<start+50;q+=5) addFlatPlane(seg,0.13,2,0,q,0.027,paint);
    for(const x of situation.mainLaneDividers||[])for(const side of [-1,1])for(let q=start+1;q<start+50;q+=5) {
      const mark=addFlatPlane(seg,.13,2,side*x*half(q)/kerb,q,.028,paint);mark.userData.roadMarking=true;
    }
  }

  function addCourtyardGateway(seg,side,z,drivewayWidth=8.4,openEntrance=false,clearYard=false) {
    // Separate arched entrances into courtyards, not a through cross street.
    const gateway=new THREE.Group();
    gateway.position.set(side*(openEntrance?13.5:10.4),0,z);
    gateway.userData.cameraOccluder=true;
    for(const end of [-1,1]) {
      const wing=createBuilding(6,openEntrance?3.2:7,openEntrance?8:11,2);
      wing.position.z=end*(drivewayWidth/2+(openEntrance?6:5.5));gateway.add(wing);
    }
    if (!openEntrance) {
    const arch=new THREE.Shape();
    const h=drivewayWidth/2;
    arch.moveTo(-h-.4,0);arch.lineTo(-h,0);arch.lineTo(-h,2.8);
    arch.quadraticCurveTo(-h,5.8,0,5.8);arch.quadraticCurveTo(h,5.8,h,2.8);
    arch.lineTo(h,0);arch.lineTo(h+.4,0);arch.lineTo(h+.4,7);arch.lineTo(-h-.4,7);arch.closePath();
    const geo=new THREE.ExtrudeGeometry(arch,{depth:6,bevelEnabled:false,curveSegments:16});
    geo.translate(0,0,-3);geo.rotateY(Math.PI/2);
    const lintel=new THREE.Mesh(geo,sceneryMat(0xD7C8AE));gateway.add(lintel);window.PDD_ROADS.skinObject(lintel,'plaster');
    const cornice=new THREE.Mesh(new THREE.BoxGeometry(6.2,.18,drivewayWidth+22),sceneryMat(0xA89C88));
    cornice.position.y=7.1;gateway.add(cornice);
    }
    gateway.userData.openEntrance=openEntrance;
    seg.add(gateway);state.occluders.push(gateway);
    // Narrow paved entrance, lowered kerb, and a courtyard enclosed at the back.
    roadSurface(seg,17,drivewayWidth,side*12.5,z);
    roadSurface(seg,12,16,side*27,z);
    for(const end of [-1,1]) {
      const fence=createFence(12);fence.rotation.y=Math.PI/2;
      fence.position.set(side*27,0,z+end*8);seg.add(fence);
      if(!clearYard){const tree=createTree('round');tree.position.set(side*29,0,z+end*10);seg.add(tree);}
    }
    // The continuation begins at the yard's back edge. Fence its sides,
    // leaving a full-width gate instead of a fence across the driving lane.
    for(const end of [-1,1]){
      const back=createFence(3.5);back.position.set(side*33,0,z+end*6.25);
      back.userData.courtyardBoundary=true;seg.add(back);
    }
    for(const end of [-1,1])for(let x=23;x<=30;x+=3.4){
      const line=addFlatPlane(seg,.09,2.7,side*x,z+end*6.3,.028,roadMarkingMat());
      line.userData.parkingMarking=true;
    }
  }

  function pavementRect(seg,width,length,x,z) {
    if(length<=0)return;
    const slab=new THREE.Mesh(new THREE.BoxGeometry(width,.18,length),new THREE.MeshLambertMaterial({color:BRAND.sidewalk}));
    slab.position.set(x,.09,z);slab.userData.surface='sidewalk';seg.add(slab);return slab;
  }
  function buildYardAfterQuestionFabric(seg,start,z,situation) {
    clearJunctionFabric(seg);
    const yardZ=z+situation.yardAfter,sides=situation.yardSides||[routeSpec(situation).maneuver==='left'?-1:1],w=5.2,r=1.5;
    const ground=addFlatPlane(seg,70,52,0,z,-.02,new THREE.MeshLambertMaterial({color:season().ground}));ground.material.userData.seasonal='ground';
    roadSurface(seg,8.4,52,0,z);roadSurface(seg,70,8.4,0,z);
    const paint=roadMarkingMat();
    for(let q=start+1;q<start+50;q+=5)if(Math.abs(q-z)>5&&Math.abs(q-yardZ)>4)addFlatPlane(seg,.13,2,0,q,.027,paint);
    for(const side of [-1,1]) {
      pavementRect(seg,3.2,18.6,side*5.8,z-16.7);
      for(const end of [-1,1])pavementRect(seg,27.6,3.2,side*21.2,z+end*5.8);
      for(const end of [-1,1])addCornerFillet(seg,side,end,4.2,4.2,z,paint);
      if(!sides.includes(side)){pavementRect(seg,3.2,18.6,side*5.8,z+16.7);continue;}
      const from=z+7.4,to=yardZ-w/2-r;
      pavementRect(seg,3.2,to-from,side*5.8,(from+to)/2);
      const after=yardZ+w/2+r;
      pavementRect(seg,3.2,z+26-after,side*5.8,(after+z+26)/2);
      for(const end of [-1,1])addCornerFillet(seg,-side,end,4.2,w/2,yardZ,paint,r);
      addCourtyardGateway(seg,side,yardZ,w,true);
    }
  }

  function addLaneQuestionEvidence(seg,z,situation) {
    const paint=roadMarkingMat();
    if(situation.asymmetricCentre) {
      addFlatPlane(seg,0.7,52,0,z,0.041,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));
      if(situation.geometry?.startsWith('courtyard_')) addFlatPlane(seg,0.13,52,-0.14,z,0.042,paint);
      else for(const side of [-1,1])addFlatPlane(seg,0.13,18,-0.14,z+side*17,0.042,paint);
      for(let q=z-25;q<z+25;q+=5)addFlatPlane(seg,0.13,2,0.14,q,0.042,paint);
    }
    if(situation.tramTracks) {
      // Two embedded tracks, level with the carriageway; factory X mirrors later.
      for(const x of [-2.5,-1.1,1.1,2.5]) {
        const rail=addFlatPlane(seg,0.075,52,x,z,0.054,new THREE.MeshLambertMaterial({color:0x929A9C}));rail.userData.tramRail=true;
      }
    }
    if(situation.junctionLaneMarking) {
      const paths=situation.junctionLaneMarkingPaths||[[[-1.8,-10],[-1.8,-2],[2,1.8],[16,1.8]]];
      for(const pts of paths) {
        const path=curve(pts.map(([x,q])=>new THREE.Vector3(x,0,z+q))),length=path.getLength();
        for(let d=1;d<length;d+=2) {
          const u=d/length,p=path.getPointAt(u),v=path.getTangentAt(u);
          const m=addFlatPlane(seg,.13,1,-p.x,p.z,.034,paint);m.rotation.z=Math.atan2(v.x,v.z);m.userData.laneGuideMarking=true;
        }
      }
    }
    if(situation.laneSign) {
      const c=document.createElement('canvas');c.width=512;c.height=256;const g=c.getContext('2d');
      g.fillStyle='#164A8D';g.fillRect(0,0,512,256);g.strokeStyle='#fff';g.lineWidth=8;g.strokeRect(6,6,500,244);
      g.lineWidth=14;g.lineJoin='round';g.lineCap='round';g.fillStyle='#fff';
      const dirs=situation.laneSign==='left_right' ? [['left','straight'],['right']] : [['left','straight'],['straight','right']];
      dirs.forEach((directions,i)=>{const x=(i+.5)*512/dirs.length;
        if(i){g.save();g.lineWidth=3;g.beginPath();g.moveTo(i*512/dirs.length,25);g.lineTo(i*512/dirs.length,230);g.stroke();g.restore();}
        for(const dir of directions){g.beginPath();g.moveTo(x,210);g.lineTo(x,125);
          if(dir==='straight'){g.lineTo(x,56);g.stroke();g.beginPath();g.moveTo(x,30);g.lineTo(x-25,64);g.lineTo(x+25,64);g.closePath();g.fill();}
          else {const sx=dir==='left'?-1:1;g.quadraticCurveTo(x,95,x+sx*28,95);g.lineTo(x+sx*55,95);g.stroke();g.beginPath();g.moveTo(x+sx*79,95);g.lineTo(x+sx*47,70);g.lineTo(x+sx*47,120);g.closePath();g.fill();}
        }
      });
      const sign=new THREE.Group(),overhead=situation.laneSignOverhead===true;
      if(overhead) {
        const half=(situation.mainWidth||8.4)/2;
        for(const x of [-half-1,half+1])modelBox(sign,[.10,5.6,.10],0x697477,x,2.8,0);
        modelBox(sign,[2*half+2,.10,.10],0x697477,0,5.5,0);
      } else {
        const post=new THREE.Mesh(new THREE.CylinderGeometry(.06,.06,4.8,8),new THREE.MeshLambertMaterial({color:0x697477}));post.position.y=2.4;sign.add(post);
      }
      const face=new THREE.Mesh(new THREE.PlaneGeometry(3,1.5),new THREE.MeshBasicMaterial({map:new THREE.CanvasTexture(c)}));face.position.set(overhead?(situation.mainWidth||8.4)/4:0,overhead?5.0:4.4,-.04);face.rotation.y=Math.PI;sign.add(face);addSignBack(face);
      sign.position.set(overhead?0:(situation.mainWidth||8.4)/2+1.2,0,z-12);sign.userData.questionEvidence=true;sign.userData.overheadLaneSign=overhead;sign.userData.laneDirections=dirs;seg.add(sign);
    }
  }

  function stopDistanceTexture(distance) {
    const c=document.createElement('canvas');c.width=256;c.height=256;
    const g=c.getContext('2d');g.fillStyle='#fff';g.fillRect(0,0,256,256);
    g.strokeStyle='#171717';g.lineWidth=8;g.strokeRect(5,5,246,246);
    g.fillStyle='#171717';g.textAlign='center';g.font='bold 62px Arial';g.fillText('STOP',128,96);
    g.font='bold 55px Arial';g.fillText(distance+' м',128,194);
    return new THREE.CanvasTexture(c);
  }

  function spawnQuestionTrain(ev) {
    const z=ev.crossingZ, departing=ev.scene.railway.trainDeparting, start=new THREE.Vector3(departing?-36:28,0,z);
    const train=addRoadActor(ev.group,{id:'road_train',type:'train',name:'Поезд',color:'#397BA3',tailColor:departing?0x3E759A:undefined},start,-Math.PI/2,
      [start,new THREE.Vector3(-320,0,z)],16);
    train.clearCrossingDistance=Math.max(0,start.x+train.halfLength+7.5);
    train.waitsForPlayer=true; ev.rail.train=train; ev.actors.push(train);
    train.mesh.userData.questionEvidence=false;
  }

  function addYieldMarkings(ev) {
    const mat=roadMarkingMat();mat.side=THREE.DoubleSide;
    const triangle=(x,z,w,len) => {
      const shape=new THREE.Shape();shape.moveTo(x-w/2,z);shape.lineTo(x+w/2,z);shape.lineTo(x,z-len);shape.closePath();
      const geo=new THREE.ShapeGeometry(shape);geo.rotateX(Math.PI/2);
      const m=new THREE.Mesh(geo,mat);m.position.y=0.043;ev.group.add(m);return m;
    };
    const z=ev.stopZ+ev.scene.yieldMarkingZ;
    triangle(-1.8,z,1.5,4);
    const inner=triangle(-1.8,z-0.16,1.1,3.25);inner.material=new THREE.MeshLambertMaterial({color:BRAND.asphalt,side:THREE.DoubleSide});inner.position.y=0.044;
    for(let x=-3.5;x<-0.3;x+=0.6) triangle(x,ev.junctionZ-4.5,0.45,0.65);
  }

  function addShoulderWorks(ev) {
    const z=ev.stopZ+18;
    // A disturbed shoulder beside an open lane, as in the source photograph.
    // Loose stones and a shallow trench read as repairs rather than a solid slab.
    const earth=new THREE.MeshLambertMaterial({color:0x927957,side:THREE.DoubleSide});
    const shape=new THREE.Shape();
    shape.moveTo(-4.55,z-5);shape.lineTo(-6.3,z-4);shape.lineTo(-6.5,z+4.5);
    shape.lineTo(-5.8,z+5.5);shape.lineTo(-4.55,z+4);shape.closePath();
    const patch=new THREE.Mesh(new THREE.ShapeGeometry(shape),earth);
    patch.rotation.x=Math.PI/2;patch.position.y=0.035;ev.group.add(patch);
    for(let i=0;i<24;i++) {
      const stone=new THREE.Mesh(new THREE.DodecahedronGeometry(.09+(i%3)*.04,0),earth);
      stone.position.set(-5.1-(i%4)*.28,.06,z-4+(i*1.37)%8);ev.group.add(stone);
    }
    for(let dz=-4;dz<=4;dz+=4){const c=createTrafficCone();c.position.set(-4.65,0,z+dz);ev.group.add(c);}
    const barrier=createRoadworksBarrier(1.8);barrier.position.set(-5.6,0,z+5);
    barrier.userData.questionEvidence=true;ev.group.add(barrier);
  }

  function addGravelPatch(ev) {
    const from=ev.stopZ+ev.scene.gravelZ,to=from+32;
    // Gravel scattered over asphalt, with fading ends rather than a dirt slab.
    const mat=new THREE.MeshLambertMaterial({color:0xB8B09D});
    const parts=[];
    for(let i=0;i<480;i++) {
      const t=(i*0.61803398875)%1,x=((i*0.754877666)%1-.5)*7.8,z=from+t*(to-from);
      const fade=Math.min(1,t*8,(1-t)*8),r=(0.035+((i*0.37)%1)*0.05)*fade;
      const stone=new THREE.Mesh(new THREE.DodecahedronGeometry(r,0),mat);stone.position.set(x,0.035+r,z);parts.push(stone);
    }
    ev.group.add(mergeStatic(parts,mat));
  }

  // Authored gentle bend, returning to the corridor axis with zero slope and
  // curvature at both ends. The geometry, actors and driving aids share it.
  function makeRoadBend(stopZ, spec) {
    const from=stopZ+spec.from, to=stopZ+spec.to, span=to-from;
    const centerAt=z=>z<=from||z>=to?0:spec.offset*Math.sin(Math.PI*(z-from)/span)**4;
    const slopeAt=z=>{
      if(z<=from||z>=to)return 0;
      const u=Math.PI*(z-from)/span;
      return spec.offset*4*Math.PI/span*Math.sin(u)**3*Math.cos(u);
    };
    return {from,to,centerAt,slopeAt};
  }

  function curvedLanePoints(bend,offset,from,to,step=2) {
    const points=[],n=Math.max(1,Math.ceil(Math.abs(to-from)/step));
    for(let i=0;i<=n;i++) { const z=from+(to-from)*i/n;points.push(new THREE.Vector3(bend.centerAt(z)+offset,0,z)); }
    return points;
  }

  function buildCurvedQuestionRoad(ev) {
    const bend=ev.curve=makeRoadBend(ev.stopZ,ev.scene.roadCurve);
    const from=ev.stopZ-34,to=ev.endZ-5;
    ev.rural=replaceCorridorStrip(from,to,g=>{
      g.userData.centerline={...bend,from,to};
      const asphalt=new THREE.MeshLambertMaterial({color:BRAND.asphalt});
      const road=addRibbon(g,from-SEAM,to+SEAM,z=>bend.centerAt(z)-4.2,z=>bend.centerAt(z)+4.2,.02,asphalt);
      road.userData.surface='road';
      // A bend's AABB also encloses grass. Use the actual lateral boundaries.
      road.userData.containsRoad=p=>p.z>=from-SEAM&&p.z<=to+SEAM&&Math.abs(p.x-bend.centerAt(p.z))<=4.2+.01;
      const paint=roadMarkingMat();
      for(const side of [-1,1]) {
        addRibbon(g,from-SEAM,to+SEAM,z=>bend.centerAt(z)+side*3.95-.075,z=>bend.centerAt(z)+side*3.95+.075,.027,paint);
        const shoulder=new THREE.MeshLambertMaterial({color:0xB4AD92});
        addRibbon(g,from,to,z=>bend.centerAt(z)+(side<0?-5.5:4.2),z=>bend.centerAt(z)+(side<0?-4.2:5.5),.015,shoulder);
        for(let z=from+5;z<to-3;z+=12) {
          const tree=createTree('pine');tree.position.set(bend.centerAt(z)+side*11,0,z);g.add(tree);
        }
      }
      // Dash positions continue in world Z; every strip bends with the asphalt.
      for(let z=from+1;z<to-2;z+=5)addRibbon(g,z,z+2,q=>bend.centerAt(q)-.065,q=>bend.centerAt(q)+.065,.027,paint,.25);
    },true);
  }

  function buildWideCityQuestion(ev) {
    const from=ev.cityFrom=ev.stopZ-34,to=ev.cityTo=ev.endZ-5;
    ev.city=replaceCorridorStrip(from,to,g=>{
      const width = ev.scene.cityWidth || 16.8;
      const half=z=>4.2+(width/2-4.2)*THREE.MathUtils.smoothstep(z,from,from+18)*(1-THREE.MathUtils.smoothstep(z,to-18,to));
      const mat=new THREE.MeshLambertMaterial({color:BRAND.asphalt}),paint=roadMarkingMat();
      for(let a=from-SEAM;a<to+SEAM;a+=2){const m=addRibbon(g,a,Math.min(a+2,to+SEAM),z=>-half(z),half,0.02,mat);m.userData.surface='road';}
      for(const sx of [-1,1]) {
        const zs=[];for(let z=from;z<to;z+=1)zs.push(z);zs.push(to);
        const sw=extrudedStripZ(zs,z=>sx<0?-half(z)-3.2:half(z),z=>sx<0?-half(z):half(z)+3.2,0.18,
          new THREE.MeshLambertMaterial({color:BRAND.sidewalk}));sw.userData.surface='sidewalk';g.add(sw);
        addEdgeLineZ(g,from-SEAM,to+SEAM,z=>sx*half(z),sx,paint);
        if ((ev.scene.cityLanes || 2) > 1) for(let z=from+20;z<to-20;z+=5)addFlatPlane(g,0.13,2,sx*4.2,z,0.03,paint);
      }
      if(ev.scene.cityCentre==='dashed') {
        for(let z=from;z<to-2;z+=5)addFlatPlane(g,0.13,2,0,z,0.03,paint);
      } else for(const x of [-0.1,0.1])addFlatPlane(g,0.13,to-from,x,(from+to)/2,0.03,paint);
    });
  }

  function addRoadLaneEvidence(ev) {
    const sc=ev.scene,paint=roadMarkingMat(),group=ev.group,z=ev.stopZ;
    if(sc.oneWayRoad) ev.oneWay=replaceCorridorStrip(z-34,ev.endZ,g=>{
      roadSurface(g,8.4,ev.endZ-z+34,0,(z-34+ev.endZ)/2);
      for(const x of [-3.95,3.95])addFlatPlane(g,.13,ev.endZ-z+34,x,(z-34+ev.endZ)/2,.03,paint);
      for(let q=z-33;q<ev.endZ;q+=5)addFlatPlane(g,.13,2,0,q,.03,paint);
    });
    if(sc.approachDivider) {
      addFlatPlane(group,.55,112,-4.2,z+44,.04,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));
      for(let q=z-12;q<z+32;q+=8)addFlatPlane(group,.13,6,-4.2,q+3,.042,paint);
      addFlatPlane(group,.13,66,-4.2,z+67,.042,paint);
    }
    if(sc.busBaySide) {
      ev.busBay=buildRoundedBusBay(z+17,sc.busBaySide,3.2);
      const shelter=createBusShelter();shelter.position.set(sc.busBaySide*10,0,z+17);group.add(shelter);
    }
    if(sc.busStopMarking) {
      const bay=ev.busBay=replaceCorridorStrip(z+2,z+34,g=>{
        const depth=q=>q<z+10?THREE.MathUtils.clamp((q-z-3)/7,0,1):q>z+26?THREE.MathUtils.clamp((z+33-q)/7,0,1):1;
        const left=q=>-4.2-depth(q);
        const road=addRibbon(g,z+2,z+34,left,()=>4.2,.02,new THREE.MeshLambertMaterial({color:BRAND.asphalt}));road.userData.surface='road';
        road.userData.containsRoad=p=>p.z>=z+2&&p.z<=z+34&&p.x>=left(p.z)&&p.x<=4.2;
        const zs=[z+2,z+3,z+10,z+26,z+33,z+34];
        const pavement=extrudedStripZ(zs,q=>left(q)-3.2,left,.18,new THREE.MeshLambertMaterial({color:season().sidewalk}));pavement.userData.surface='sidewalk';g.add(pavement);
        roadSurface(g,3.2,32-SEAM,5.8,z+18,true);
        for(let q=z+3;q<z+33;q+=5)addFlatPlane(g,.13,2,0,q,.03,paint);
        // Edge lines go on as on the road: solid opposite, broken along the stop.
        addEdgeLineZ(g,z+2-SEAM,z+34+SEAM,()=>4.2,1,paint);
        addEdgeLineZ(g,z+2-SEAM,z+3.5,()=>-4.2,-1,paint);addEdgeLineZ(g,z+32.5,z+34+SEAM,()=>-4.2,-1,paint);
        for(let q=z+4.5;q<z+31.5;q+=3)addFlatPlane(g,.15,1.5,-3.95,q+.75,.028,paint);
        const yellow=new THREE.MeshBasicMaterial({color:0xF2C635});
        const points=[];for(let q=z+6;q<=z+30;q+=2)points.push(new THREE.Vector3(left(q)+(points.length%2?1.6:.25),.035,q));
        for(let i=1;i<points.length;i++) {
          const line=new THREE.LineCurve3(points[i-1],points[i]);
          const stroke=new THREE.Mesh(new THREE.TubeGeometry(line,1,.065,4,false),yellow);stroke.userData.busStopZigzag=true;g.add(stroke);
        }
      },false);
      bay.userData.busStopBay=true;
    }
  }

  function checkRoadLaneRules(ev) {
    const p=playerCarGroup.position,old=ev.lanePrevious||p.clone();
    if(ev.scene.oneWayRoad && p.z>=ev.stopZ+10 && Math.cos(playerCarGroup.rotation.y)<-.3 && !ev.laneFault) {
      ev.laneFault=true;roadViolation('wrong_maneuver');
    }
    const yaw=playerCarGroup.rotation.y;
    if(Math.abs(Math.sin(yaw))>.35 && ev.turnStartedZ===undefined) ev.turnStartedZ=p.z;
    if(Math.cos(yaw)>.9 && Math.abs(Math.sin(yaw))<.15) ev.turnStartedZ=undefined;
    const zone=ev.scene.forbidUturn;
    const insideStop=q=>q!==undefined && q>=ev.stopZ+zone[0] && q<=ev.stopZ+zone[1];
    if(zone && (insideStop(p.z)||insideStop(ev.turnStartedZ)) && Math.cos(yaw)<-.3 && !ev.laneFault) {
      ev.laneFault=true;roadViolation('wrong_maneuver');
    }
    const extent=playerCarGroup.userData.halfWidth*Math.abs(Math.cos(yaw))+playerCarGroup.userData.halfLength*Math.abs(Math.sin(yaw));
    const oldYaw=ev.lanePreviousYaw??yaw;
    const oldExtent=playerCarGroup.userData.halfWidth*Math.abs(Math.cos(oldYaw))+playerCarGroup.userData.halfLength*Math.abs(Math.sin(oldYaw));
    for(const line of ev.scene.solidDividers||[]) {
      const side=Math.sign(old.x-line.x),before=side*(old.x-line.x)-oldExtent,after=side*(p.x-line.x)-extent;
      if(side && before>0 && after<=0) {
        const t=before/(before-after),atZ=old.z+(p.z-old.z)*t;
        if(atZ>=ev.stopZ+line.fromZ && atZ<=ev.stopZ+line.toZ && !ev.laneFault) {ev.laneFault=true;roadViolation('wrong_maneuver');}
      }
    }
    ev.lanePreviousYaw=yaw;
    ev.lanePrevious=p.clone();
  }

  function addQuestionBus(ev) {
    const V=(x,dz)=>new THREE.Vector3(x,0,ev.stopZ+dz),curb=ev.scene.busPriority?-6.8:-4.0,p=V(curb,ev.scene.busPriority?11:16);
    const bus=addRoadActor(ev.group,{id:'question_bus',type:ev.scene.busPriority?'bus':'van',name:'Автобус',question:true,color:ev.scene.busPriority?'#2BC280':'#E8EAEC'},p,0,
      ev.scene.busPriority ? [p,V(-6.8,13),V(-5.4,17),V(-1.8,24),V(-1.8,45),V(-1.8,320)]
        : [p,V(curb,20),V(-3.2,30),V(-1.8,45),V(-1.8,320)],10,[{from:0,to:34,side:'left'}]);
    bus.clearDistance=46;bus.stopAtDistance=0;bus.stopFor=Infinity;ev.bus=bus;ev.actors.push(bus);
    if(ev.scene.busPriority){
      // The photographed car blocks the curb lane ahead of the departing bus.
      const p=V(-5.7,29),cfg={id:'bus_lane_obstacle',type:'car',name:'Автомобиль',question:true,color:'#9D5042'};
      const car=addRoadActor(ev.group,cfg,p,Math.PI*.38,[p,p.clone().add(new THREE.Vector3(.01,0,0))],0);
      car.mesh.userData.blinkerSide='hazard';ev.actors.push(car);
      const shelter = createBusShelter(); shelter.position.set(-10.0,0,ev.stopZ+9); ev.group.add(shelter);
    }
  }
  function updateQuestionBus(ev,dt) {
    const bus=ev.bus;
    if(bus.stopFor===Infinity && (ev.scene.busPriority || playerCarGroup.position.z>ev.stopZ+34))bus.stopFor=0;
    if(ev.scene.busPriority && !bus.cleared && state.speed>0.5 && conflictAhead(playerFootprint(),bus) && !ev.priorityPenalized){
      ev.priorityPenalized=true;roadViolation('priority');
    }
  }
  function addQuestionPolice(ev) {
    // The event is built well before the player reaches stopZ. A position
    // relative to stopZ would put a stationary police car in their way.
    const p=new THREE.Vector3(-1.8,0,Math.min(playerCarGroup.position.z-24,ev.stopZ-10));
    const car=addRoadActor(ev.group,{id:'question_police',type:'special',name:'Полиция',color:'#FFFFFF',question:true,beacon:'blue_red',siren:true},p,0,
      [p,new THREE.Vector3(-1.8,0,ev.stopZ+320)],18);
    car.waitsForPlayer=false;ev.police=car;ev.actors.push(car);
  }
  function updateQuestionPolice(ev,dt) {
    const car=ev.police;
    if(playerCarGroup.position.x<-4.5){ev.policeYielded=true;car.stopFor=0;}
    if(!ev.policeYielded){
      ev.policeWait=(ev.policeWait||0)+dt;
      if(ev.policeWait>5 && !ev.priorityPenalized){ev.priorityPenalized=true;roadViolation('priority');}
    }
  }

  function createChevronBarrier(width) {
    const barrier=createRoadworksBarrier(width),canvas=document.createElement('canvas');canvas.width=512;canvas.height=96;
    const ctx=canvas.getContext('2d');ctx.fillStyle='#D43C36';ctx.fillRect(0,0,512,96);ctx.fillStyle='#F7F4EC';
    for(let x=0;x<512;x+=96){ctx.beginPath();ctx.moveTo(x+65,0);ctx.lineTo(x+18,48);ctx.lineTo(x+65,96);ctx.lineTo(x+94,96);ctx.lineTo(x+47,48);ctx.lineTo(x+94,0);ctx.closePath();ctx.fill();}
    const face=new THREE.Mesh(new THREE.PlaneGeometry(width,.55),new THREE.MeshBasicMaterial({map:new THREE.CanvasTexture(canvas),side:THREE.DoubleSide}));
    face.position.set(0,1.12,-.13);face.rotation.y=Math.PI;barrier.add(face);barrier.userData.chevrons='left';return barrier;
  }

  function buildTemporaryBypass(ev) {
    const from=ev.stopZ-34,to=ev.endZ-5;
    ev.bypassFrom=ev.stopZ+40;ev.bypassTo=ev.stopZ+150;
    const gap1=[ev.stopZ+42,ev.stopZ+64],gap2=[ev.stopZ+126,ev.stopZ+148];
    ev.bypass=replaceCorridorStrip(from,to,g=>{
      const widen=z=>THREE.MathUtils.smoothstep(z,from,from+22)*(1-THREE.MathUtils.smoothstep(z,to-22,to));
      const ownAsphalt=new THREE.MeshLambertMaterial({color:BRAND.asphalt});
      for(let z=from;z<to;z+=2){const m=addRibbon(g,z,Math.min(z+2,to),q=>-4.2-4.2*widen(q),q=>4.2*(1-widen(q)),0.02,ownAsphalt);m.userData.surface="road";}
      // Second carriageway separates gradually; the median has two actual openings.
      const offset=z=>2*THREE.MathUtils.smoothstep(z,from,from+22)*(1-THREE.MathUtils.smoothstep(z,to-22,to));
      const asphalt=new THREE.MeshLambertMaterial({color:BRAND.asphalt}),paint=roadMarkingMat();
      for(let z=from;z<to;z+=2){const end=Math.min(z+2,to),m=addRibbon(g,z,end,q=>offset(q),q=>offset(q)+8.4,0.021,asphalt);m.userData.surface='road';}
      for(const [a,b] of [gap1,gap2]) roadSurface(g,2.05,b-a,1,(a+b)/2);
      for(const [a,b] of [[from,gap1[0]],[gap1[1],gap2[0]],[gap2[1],to]]){
        const m=addRibbon(g,a,b,()=>0,offset,0.18,new THREE.MeshLambertMaterial({color:season().ground}));m.userData.surface='sidewalk';
      }
      for(let z=from+24;z<to-24;z+=5)addFlatPlane(g,0.13,2,-4.2,z,0.029,paint);
      // Edge lines along both outer kerbs, following the widening.
      addEdgeLineZ(g,from-SEAM,to+SEAM,q=>-4.2-4.2*widen(q),-1,paint);addEdgeLineZ(g,from-SEAM,to+SEAM,q=>offset(q)+8.4,1,paint);
      const closed=createChevronBarrier(8.4);closed.position.set(-4.2,0,ev.stopZ+58);g.add(closed);
      state.props.push({mesh:closed,radius:4.2,depth:0.3,kind:'barrier',ev,root:g});
      for(let z=ev.stopZ+54;z<ev.stopZ+125;z+=6){const cone=createTrafficCone();cone.position.set(-0.3,0,z);g.add(cone);}
      for(let z=gap1[0];z<=gap2[1];z+=5)addFlatPlane(g,0.13,2,6.2,z,0.028,paint);
    },true);
    const warning=addRoadSign(ev.group,'3.2',ev.stopZ+57,'right',null,-4.2);warning.userData.questionEvidence=true;
    const p=new THREE.Vector3(8,0,ev.stopZ+44);
    const car=addRoadActor(ev.group,{id:'bypass_oncoming',type:'car',name:'Встречный',color:'#2BC280',question:true},p,Math.PI,
      [p,new THREE.Vector3(8,0,ev.stopZ-34)],6);ev.actors.push(car);
    ev.guide=createRouteGuide([curve([[-1.8,15],[-1.8,39],[1,50],[4,60],[4,124],[1,136],[-1.8,147]].map(([x,z])=>new THREE.Vector3(x,0.12,ev.stopZ+z)))]);
    ev.guide.userData.questionEvidence=true;ev.group.add(ev.guide);ev.guide.visible=false;
  }
  function updateTemporaryBypass(ev) {
    const p=playerCarGroup.position;
    if(p.z>ev.stopZ+56 && p.z<ev.stopZ+125 && p.x<0 && !ev.priorityPenalized){ev.priorityPenalized=true;roadViolation('roadworks');}
    // Temporary assigned lane is 2..6.2 m; the opposing outer lane remains opposing.
    if(p.z>ev.bypassFrom && p.z<ev.bypassTo && p.x>6.2 && !ev.oncomingPenalized){ev.oncomingPenalized=true;roadViolation('oncoming');}
  }

  function buildQuestionEvent(group, boundary, situation) {
    const sc = situation.scene;
    // Far enough past the junction that anything the question rebuilds
    // (rural stretch, motorway, side junction, markings) is out of the
    // camera's view when it is laid: the player never sees the road change.
    const stopZ = boundary + 110;
    // The stretch a question owns: its zone, or past its railway crossing.
    const span = Math.max(120, sc.zoneLength || 0, sc.railway ? sc.railway.z + (sc.railway.after ?? 30) : 0);
    const ev = { group, situation, kind: sc.kind, scene: sc, stopZ, startZ: stopZ, endZ: stopZ + span,
      phase: 'approach', actors: [], overtakePenalized: false };
    // The stretch belongs to this question: the next ticket junction comes after it.
    extendQuestionCorridor(stopZ + Math.max(span, sc.motorway ? 175 : 0) + 45);
    // The rural stretch goes first: a junction or a crossing inside it is
    // laid over it, and no roadside pine stands where they are.
    const keepClear = [sc.junction && stopZ + sc.junction.z, sc.railway && stopZ + sc.railway.z].filter(Boolean);
    if (sc.roadCurve) {
      buildCurvedQuestionRoad(ev);
    } else if (sc.outsideSettlement) {
      ev.rural = replaceCorridorStrip(stopZ - 34, ev.endZ - 5, g => {
        const from = stopZ - 34, to = ev.endZ - 5, length = to - from;
        roadSurface(g, 8.4, length, 0, (from + to) / 2);
        const paint = roadMarkingMat();
        if(!sc.unmarkedRoad) {
          for (const x of [-3.95, 3.95]) addFlatPlane(g, 0.15, length, x, (from + to) / 2, 0.027, paint);
          for (let z = from + 1; z < to - 2; z += 5) addFlatPlane(g, 0.13, 2, 0, z, 0.027, paint);
        }
        for (const side of [-1, 1]) for (let z = from + 5; z < to - 3; z += 12) {
          if (keepClear.some(c => Math.abs(z - c) < 13)) continue;
          const tree = createTree('pine'); tree.position.set(side * 11, 0, z); g.add(tree);
        }
      }, true);
    }
    if (sc.wideCity) buildWideCityQuestion(ev);
    addRoadLaneEvidence(ev);
    if (sc.kind === "temporary_bypass") buildTemporaryBypass(ev);
    if (sc.junction) buildRoadQuestionJunction(ev);
    if (sc.railway) buildRailwayCrossing(ev);
    if (sc.motorway) buildQuestionMotorway(ev);
    if (sc.approachLimitKmH) state.speedLimitKmH = sc.approachLimitKmH;
    const [town, nextTown] = townPair();
    ev.towns = [town, nextTown];
    (sc.signs || []).forEach((sg, i) => {
      const sign = addRoadSign(group, sg.code, stopZ + sg.z, sg.side, sg.stopDistance ? 'STOP · ' + sg.stopDistance + ' м' : sg.plate || null, sg.offsetX || 0, sg.speedValue ?? null,
        sg.code === '5.23.1' ? nextTown : town, sg.plateSign || null);
      if (sg.stopDistance) {
        const plate = group.children.at(-1);
        const face = plate.children.find(o => o.geometry?.type === 'PlaneGeometry');
        face.material.map = stopDistanceTexture(sg.stopDistance);
        face.geometry = new THREE.PlaneGeometry(0.95,0.95);
        if(face.userData.back) face.userData.back.geometry=face.geometry;
      }
      sign.userData.editKey = 'sign:' + i; sign.userData.signCode = sg.code;
    });
    if (sc.kind === 'speed') {
      ev.signZ = stopZ + (sc.signs?.find(s => s.z >= 0)?.z ?? 12);
      if (sc.zoneLength) ev.endZ = stopZ + sc.zoneLength;
      // The zone ends with its counterpart sign (5.22, 5.2, 5.26, 5.23.1):
      // past it the built-up limit applies again, as the rules require.
      if (sc.endSign) {
        ev.endSignZ = ev.endZ - 6;
        const end = addRoadSign(group, sc.endSign, ev.endSignZ, 'right', null, 0, null, nextTown);
        end.userData.editKey = 'sign:end'; end.userData.signCode = sc.endSign;
      }
    }
    if (sc.marking) addCentreMarking(group, stopZ - 12, ev.endZ, sc.marking);
    if (sc.kind === 'detour') {
      // A roadworks barrier across the player's lane with 4.2.2 on it (35.5):
      // the sign says round it on the left, over the solid line (signs take
      // precedence over markings). Hitting it is a roadworks fault.
      ev.obstZ = stopZ + sc.obstacleZ;
      const width = sc.obstacleWidth ?? 3.2;
      const barrier = createRoadworksBarrier(width);
      barrier.position.set(sc.obstacleX ?? -1.8, 0, ev.obstZ);
      barrier.userData.questionEvidence = true;
      group.add(barrier);
      state.props.push({ mesh: barrier, radius: width / 2, depth: 0.3, kind: 'barrier', ev, root: group });
      const onBarrier = createRoadSign('4.2.2', 2.4);
      onBarrier.children.filter(o => o.geometry?.type === 'CylinderGeometry').forEach(o => { o.visible = false; });
      // Mounted on the board: a knocked barrier takes its sign with it.
      onBarrier.scale.setScalar(0.9); onBarrier.position.set(0, -1.1, -0.06);
      onBarrier.userData.questionEvidence = true;
      barrier.userData.parts.at(-1).add(onBarrier);
    }
    if (sc.trajectories?.length) {
      const paths = sc.trajectories.map(t => curve(t.points.map(([x, z]) => new THREE.Vector3(x, 0.12, stopZ + z))));
      const guide = createRouteGuide(paths);
      sc.trajectories.forEach((t, i) => {
        if (!t.label) return;
        const label = createLetterToken(t.label);
        const at = t.labelPosition
          ? new THREE.Vector3(t.labelPosition[0], 0.8, stopZ + t.labelPosition[1])
          : paths[i].getPointAt(1).add(new THREE.Vector3(0, 0.8, 2));
        label.position.copy(at); guide.add(label);
      });
      // Include the complete alternatives in camera framing, not just the sign.
      guide.userData.questionEvidence = true;
      group.add(guide); guide.visible = false;
      ev.guide = guide;
    }
    if (sc.crosswalkZ !== undefined) { ev.crosswalkZ = stopZ + sc.crosswalkZ; addZebra(group, ev.crosswalkZ); }
    // Different centre lines before and after a crossing (13_11): the zebra
    // itself stays unmarked, as on the road.
    if (sc.markingBefore) addCentreMarking(group, stopZ - 12, ev.crosswalkZ - 2.6, sc.markingBefore);
    if (sc.markingAfter) addCentreMarking(group, ev.crosswalkZ + 2.6, ev.endZ, sc.markingAfter);
    (sc.vehicles || []).forEach((v, i) => {
      const cfg = { id: `road_${i}_${v.type}`, type: v.type, name: v.name, color: v.color, question: true,
        badge: v.badge, paint: v.paint, blinker: v.blinker, maneuver: v.maneuver, scale: v.scale, approach: v.lane };
      if (v.lane === 'right') {
        // From the driver's right, heading left across the road: keeping to
        // its own right it uses the far half of the side street (+Z).
        const p = new THREE.Vector3(v.x ?? -15, 0, ev.junctionZ + 1.8);
        const actor = addRoadActor(group, cfg, p, Math.PI / 2,
          [p, new THREE.Vector3(12, 0, p.z), new THREE.Vector3(34, 0, p.z)], v.speed);
        actor.clearDistance = 24;
        ev.actors.push(actor);
      } else if (v.lane === 'oncoming') {
        const p = new THREE.Vector3(1.8, 0, stopZ + v.z);
        const points=ev.curve ? curvedLanePoints(ev.curve,1.8,p.z,p.z-280) :
          [p,p.clone().add(new THREE.Vector3(0,0,-90)),p.clone().add(new THREE.Vector3(0,0,-280))];
        p.copy(points[0]);
        ev.actors.push(addRoadActor(group,cfg,p,Math.PI+(ev.curve?Math.atan(ev.curve.slopeAt(p.z)):0),points,v.speed));
      } else {
        const p = new THREE.Vector3(v.x ?? -1.8, 0, stopZ + v.z);
        const V = (x, z) => new THREE.Vector3(x, 0, z);
        if (v.maneuver === 'turn_left_at_junction') {
          // A signalled left turn happens at the next junction (its centre is
          // 226 m past the seam) and the signal goes off once the turn is done.
          const c = ev.junctionZ ?? boundary + 226;
          const points = [p, V(-1.8, c - 30), V(-1.8, c - 6), V(-1.8, c - 1.5), V(1.5, c + 1.8), V(22, c + 1.8), V(90, c + 1.8)];
          const actor = addRoadActor(group, cfg, p, 0, points, v.speed);
          const turnEnd = actor.path.getLength() - 68;
          actor.signalPlan = [{ from: 0, to: turnEnd - 14, side: 'left' }];
          actor.holdSpeedUntil = turnEnd + 8;
          ev.actors.push(actor);
        } else if (v.maneuver === 'overtake' && v.joinsAtQuestion) {
          // Comes up from behind while the camera frames the question (never
          // seen appearing), waits behind the player signalling left, and
          // overtakes briskly once the question is answered.
          ev.joiners = ev.joiners || [];
          ev.joiners.push(() => {
            const z0 = stopZ - 9, start = V(-1.8, z0 - 31);
            const actor = addRoadActor(group, cfg, start, 0, [start, V(-1.8, z0), V(1.8, z0 + 14), V(1.8, z0 + 90),
              V(-1.8, z0 + 110), V(-1.8, z0 + 420)], Math.max(v.speed, 14));
            actor.stopAtDistance = 31; actor.stopFor = Infinity; actor.waitsForPlayer = false;
            actor.signalPlan = [{ from: 0, to: 52, side: 'left' }, { from: 112, to: 136, side: 'right' }];
            actor.passedAt = 125;
            ev.actors.push(actor);
          });
        } else if (v.maneuver === 'overtake') {
          // Pulls out into the oncoming lane, passes the vehicle ahead and
          // returns: left signal out, right signal back, then nothing.
          // Already over the centre line, or (as in the ticket photo) still in
          // the lane with the left signal on: it pulls out once released.
          const points = v.alreadyOvertaking && p.x > 0
            ? [p, V(1.8, p.z + 12), V(1.8, p.z + 62), V(-1.8, p.z + 82), V(-1.8, p.z + 120), V(-1.8, p.z + 320)]
            : [p, V(-1.8, p.z + 8), V(1.8, p.z + 22), V(1.8, p.z + 62), V(-1.8, p.z + 78), V(-1.8, p.z + 120), V(-1.8, p.z + 320)];
          // The overtaking vehicle is clearly faster than the one it passes,
          // so the manoeuvre actually completes on screen.
          const actor = addRoadActor(group, cfg, p, 0, points, Math.max(v.speed * 1.6, 13));
          actor.signalPlan = [{ from: 0, to: 20, side: 'left' }, { from: 56, to: 80, side: 'right' }];
          actor.passedAt = 90;
          ev.actors.push(actor);
        } else {
          const actor = addRoadActor(group, cfg, p, 0,
            [p, p.clone().add(new THREE.Vector3(0, 0, 60)), p.clone().add(new THREE.Vector3(0, 0, 320))], v.speed);
          // Standing at a closed crossing: it goes once the boom is up.
          if (v.waitsAtCrossing) { actor.stopAtDistance = 0; actor.stopFor = Infinity; }
          ev.actors.push(actor);
        }
      }
    });
    if (sc.railway?.train) spawnQuestionTrain(ev);
    if (sc.yieldMarkingZ !== undefined) addYieldMarkings(ev);
    if (sc.shoulderWorks) addShoulderWorks(ev);
    if (sc.gravelZ !== undefined) addGravelPatch(ev);
    if (sc.kind === 'bus_departure') addQuestionBus(ev);
    if (sc.kind === 'emergency_lane') addQuestionPolice(ev);
    if(ev.curve) group.children.filter(o=>!o.userData.actor).forEach(o=>{
      const z=o.position.z;
      o.position.x+=ev.curve.centerAt(z);
      o.rotation.y+=Math.atan(ev.curve.slopeAt(z));
    });
    applySceneEdits(group, situation.id, stopZ);
    const crossTraffic = ev.actors.filter(a => a.config.approach === 'right' && sc.junction?.priority === 'equal');
    if (crossTraffic.length) ev.actors.filter(a => !crossTraffic.includes(a)).forEach(a => { a.dependencies = crossTraffic; });
    state.weatherDirty = true;
    applyWeather();
    return ev;
  }

  // A bus bay on the right with a shelter and sign 5.16: a bus pulls in,
  // waits a few seconds and merges back. No question, no gameplay rule.
  function buildRoundedBusBay(z, side, depth=2.8) {
    const profile=q=>depth*(1-THREE.MathUtils.smoothstep(Math.abs(q-z),11,20));
    const bay=replaceCorridorStrip(z-26,z+26,g=>{
      const low=q=>-4.2-(side<0?profile(q):0),high=q=>4.2+(side>0?profile(q):0);
      const road=addRibbon(g,z-26-SEAM,z+26+SEAM,low,high,.02,new THREE.MeshLambertMaterial({color:BRAND.asphalt}),.5);
      road.userData.surface='road';road.userData.containsRoad=p=>p.x>=low(p.z)&&p.x<=high(p.z);
      const zs=[];for(let q=z-26;q<=z+26;q+=.5)zs.push(q);
      for(const edgeSide of [-1,1]) {
        const edge=edgeSide<0?low:high;
        const slab=extrudedStripZ(zs,q=>edge(q)+(edgeSide<0?-3.2:0),q=>edge(q)+(edgeSide>0?3.2:0),.18,new THREE.MeshLambertMaterial({color:season().sidewalk}));
        slab.userData.surface='sidewalk';g.add(slab);
      }
      const paint=roadMarkingMat();
      for(let q=z-25;q<z+25;q+=5)addFlatPlane(g,.13,2,0,q,.028,paint);
      // Edge lines go on as on the road; along the pocket a broken line.
      addEdgeLineZ(g,z-26-SEAM,z+26+SEAM,()=>-side*4.2,-side,paint);
      addEdgeLineZ(g,z-26-SEAM,z-19.5,()=>side*4.2,side,paint);addEdgeLineZ(g,z+19.5,z+26+SEAM,()=>side*4.2,side,paint);
      for(let q=z-19;q<z+19;q+=3)addFlatPlane(g,.15,1.5,side*3.95,q,.028,paint);
    });
    bay.userData.busStopBay=true;bay.userData.baySide=side;return bay;
  }

  function buildBusStopEvent(group, bayZ) {
    const ev = { group, kind: 'busstop', phase: 'approach', actors: [], bayZ };
    const asphalt = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
    const bay = buildRoundedBusBay(bayZ, -1);
    clearRoadside(bayZ);
    // Shelter behind the path, bench, and the stop sign at the head of the bay.
    const dark = sceneryMat(0x3B4450), glassMat = new THREE.MeshLambertMaterial({ color: 0x9DB8C6, transparent: true, opacity: 0.55 });
    const roof = new THREE.Mesh(new THREE.BoxGeometry(1.6, 0.1, 4.2), dark); roof.position.set(-10.4, 2.5, bayZ); group.add(roof);
    [-1.9, 1.9].forEach(dz => { const post = new THREE.Mesh(new THREE.BoxGeometry(0.08, 2.5, 0.08), dark); post.position.set(-11.0, 1.25, bayZ + dz); group.add(post); });
    const back = new THREE.Mesh(new THREE.BoxGeometry(0.05, 2.1, 4.0), glassMat); back.position.set(-11.15, 1.3, bayZ); group.add(back);
    const bench = new THREE.Mesh(new THREE.BoxGeometry(0.5, 0.1, 3), sceneryMat(0x987856)); bench.position.set(-10.6, 0.55, bayZ); group.add(bench);
    // 5.16 stands at the entry to the pocket, on the road side of the path.
    addRoadSign(group, '5.16', bayZ - 17, 'right', null, -1.9);
    refreshRoadBounds();
    // The bus is already standing in the bay when it comes into view (it
    // used to be spawned in the lane ahead, sometimes right in front of the
    // player); it pulls out once the player is close.
    const V = (x, z) => new THREE.Vector3(x, 0, z);
    const p = V(-5.5, bayZ - 2);
    const cfg = { id: 'road_bus', type: 'bus', name: 'Автобус', color: '#FFA53C' };
    const bus = addRoadActor(group, cfg, p, 0, [p, V(-5.5, bayZ + 4), V(-3.6, bayZ + 17), V(-2.6, bayZ + 23), V(-1.8, bayZ + 40), V(-1.8, bayZ + 300)], 9);
    bus.stopAtDistance = 0; bus.stopFor = Infinity;
    ev.actors.push(bus);
    state.busBays.push({ mesh: bay, center: new THREE.Vector3(-5.5, 0, bayZ) });
    return ev;
  }
  // 1 beside a bus pocket, 0 away from it, smooth in between (pavement edge
  // and the walkers' line follow it).
  function bayProfile(dz) { return 1 - THREE.MathUtils.smoothstep(Math.abs(dz), 14, 25); }
  // Remove houses, fences, trees and parked cars from the exit road's right
  // side around a bus bay, so the shelter and the path get a clear lot.
  function clearRoadside(bayZ, half = 30, xMin = -13, xMax = -7) {
    const seg = state.exitRoad;
    if (!seg) return;
    seg.updateMatrixWorld(true);
    const doomed = [];
    // A stretch added to this road for a long question and a question's own
    // crossing are pieces of the road itself, not roadside objects: clear
    // inside them. Taking one away whole left a gap with no asphalt ahead.
    const visit = group => group.children.forEach(o => {
      if (o.userData.roadEnds || o.userData.questionTopology) { visit(o); return; }
      if (o.userData.surface || o.userData.baked || o.isLine || o.userData.puddle) return;
      if (state.ambient.some(a => a.mesh === o)) return;
      const box = new THREE.Box3().setFromObject(o);
      if (box.isEmpty()) return;
      // Anything that reaches into the lot (path, shelter and a margin),
      // not only objects centred there: a long house must not cover the path.
      if (box.max.x > xMin && box.min.x < xMax && box.max.z > bayZ - half && box.min.z < bayZ + half && box.max.y > 0.3) doomed.push(o);
    });
    visit(seg);
    doomed.forEach(o => { o.parent.remove(o); state.occluders = state.occluders.filter(b => b !== o); });
  }
  // Vehicles coming the other way on a straight: they pass and vanish behind.
  function addOncomingTraffic(group, boundary, scene) {
    // Overtaking questions author their own traffic; never add random cars there.
    if (scene && (scene.kind !== 'speed' || scene.motorway)) return;
    const V = (x, z) => new THREE.Vector3(x, 0, z);
    const kinds = [['car', 'Встречный', '#2BC280'], ['car', 'Встречный', '#6E86A6'], ['truck', 'Грузовик', '#9AA0A6'],
      ['tractor', 'Трактор', '#F2B233'], ['motorcycle', 'Мотоцикл', '#8B5CF6'], ['bus', 'Автобус', '#FFA53C']];
    const n = 1 + (Math.random() < 0.4 ? 1 : 0);
    for (let i = 0; i < n; i++) {
      const [type, name, color] = kinds[Math.floor(Math.random() * kinds.length)];
      const z = boundary + 140 + i * 45 + Math.random() * 30;
      const p = V(1.8, z);
      const actor = addRoadActor(group, { id: `road_oncoming_${i}`, type, name, color, badge: type === 'tractor' ? 'Трактор' : undefined },
        p, Math.PI, [p, V(1.8, z - 60), V(1.8, boundary + 2)], type === 'tractor' ? 5 : type === 'truck' || type === 'bus' ? 10 : 12);
      actor.waitsForPlayer = false; // already on the move
    }
  }

  // Unregulated zebra without a question: a pedestrian steps out when the
  // player approaches; passing the crossing while they are on the carriageway
  // is a 'pedestrian' violation (14.1), a hit is an ordinary collision.
  // Speed hump (5.20) across the whole carriageway: a low yellow/black
  // cylinder top. Cars rise over it; no speed penalty, just a nudge.
  function addSpeedHump(group, z) {
    const r = 1.0, h = 0.15, pieces = 8, width = 8.4 / pieces;
    let piece;
    for (let i = 0; i < pieces; i++) {
      const g = new THREE.CylinderGeometry(r, r, width, 20, 1, false, -0.55, 1.1);
      g.rotateZ(Math.PI / 2); g.rotateX(-Math.PI / 2); // axis across the road, arc on top
      piece = new THREE.Mesh(g, sceneryMat(i % 2 ? 0x22262A : 0xF2C230));
      piece.position.set(-4.2 + width * (i + 0.5), 0.02 + h - r, z);
      piece.receiveShadow = true;
      group.add(piece);
    }
    const marker = new THREE.Object3D(); marker.position.set(0, 0, z); group.add(marker);
    state.humps.push({ marker, r, h, piece });
  }
  // Height of the road surface under a point (world), humps included.
  function humpHeight(p) {
    let y = 0;
    for (const hump of state.humps) {
      const at = hump.marker.getWorldPosition(new THREE.Vector3());
      if (clippedAway(hump.piece?.material, at)) continue;
      const d = Math.abs(p.z - at.z);
      if (d < hump.r && Math.abs(p.x - at.x) < 4.3) y = Math.max(y, Math.sqrt(hump.r * hump.r - d * d) - (hump.r - hump.h));
    }
    return y;
  }
  // The body rides over humps: height and pitch from both axles.
  function updateBodyOverHumps() {
    state.humps = state.humps.filter(h => h.marker.parent && h.marker.parent.parent);
    const car = playerCarGroup;
    car.rotation.order = 'YXZ';
    if (!state.humps.length) { car.position.y = 0; car.rotation.x = 0; return; }
    const fwd = new THREE.Vector3(Math.sin(car.rotation.y), 0, Math.cos(car.rotation.y));
    const base = (car.userData.halfLength || 2) * 0.62;
    const yF = humpHeight(car.position.clone().addScaledVector(fwd, base));
    const yR = humpHeight(car.position.clone().addScaledVector(fwd, -base));
    car.position.y = (yF + yR) / 2;
    car.rotation.x = -Math.atan2(yF - yR, 2 * base);
  }

  function buildCrosswalkEvent(group, crosswalkZ) {
    const ev = { group, kind: 'crosswalk', crosswalkZ, phase: 'approach', actors: [], passedZ: null };
    addZebra(group, crosswalkZ);
    // Humps on both approaches to the zebra, each with its 5.20 sign.
    addSpeedHump(group, crosswalkZ - 9);
    addSpeedHump(group, crosswalkZ + 9);
    addRoadSign(group, '5.20', crosswalkZ - 9, 'right');
    addRoadSign(group, '5.20', crosswalkZ + 9, 'left').rotation.y = Math.PI;
    addRoadSign(group, '5.19.1', crosswalkZ - 2.6, 'right');
    addRoadSign(group, '5.19.2', crosswalkZ + 2.6, 'left');
    const start = new THREE.Vector3(-6.2, 0.18, crosswalkZ);
    const cfg = { id: 'road_pedestrian', type: 'pedestrian', name: 'Пешеход', color: '#0574F8' };
    ev.pedestrian = addRoadActor(group, cfg, start, Math.PI / 2, [start,
      new THREE.Vector3(-4.4, 0.03, crosswalkZ), new THREE.Vector3(4.4, 0.03, crosswalkZ),
      new THREE.Vector3(6.2, 0.18, crosswalkZ), new THREE.Vector3(6.2, 0.18, crosswalkZ + 3),
      new THREE.Vector3(6.2, 0.18, crosswalkZ + 60)], 1.9);
    ev.actors.push(ev.pedestrian);
    return ev;
  }

  // Road works in the right lane: 1.25 and 4.2.2 (detour on the left, the
  // oncoming lane may be used for it), a taper of cones, a barrier, and behind
  // it a crew repairing a manhole — one lays fresh asphalt, one works down
  // the open hatch. Cones and the barrier are knocked flying if hit.
  function buildRoadworksEvent(group, workZ) {
    const ev = { group, kind: 'roadworks', workZ, phase: 'approach', actors: [], zoneEnd: workZ + 16 };
    // Traffic drives round the closed lane (cones, barrier, crew, hatch).
    addBlocker(group, -3.9, 0.2, workZ - 19, workZ + 21);
    addRoadSign(group, '1.25', workZ - 30, 'right');
    addRoadSign(group, '4.2.2', workZ - 3, 'right', null, 1.3);
    const prop = (mesh, radius, kind) => { state.props.push({ mesh, radius, kind, ev, root: group }); };
    // The taper closes the whole lane, from the kerb to the lane line.
    for (let i = 0; i < 6; i++) {
      const cone = createTrafficCone();
      cone.position.set(-3.8 + i * 0.66, 0, workZ - 18 + i * 3.2);
      group.add(cone); prop(cone, 0.2, 'cone');
    }
    const barrier = createRoadworksBarrier(3.2);
    barrier.position.set(-1.8, 0, workZ);
    group.add(barrier);
    state.props.push({ mesh: barrier, radius: 1.6, depth: 0.3, kind: 'barrier', ev, root: group });
    // The closed zone: a fresh asphalt patch around the manhole.
    const patch = addFlatPlane(group, 3.0, 7.5, -1.9, workZ + 7, 0.03, new THREE.MeshLambertMaterial({ color: 0x2B3036 }));
    patch.userData.freshAsphalt = true;
    const hatchZ = workZ + 9.5;
    const hole = new THREE.Mesh(new THREE.CircleGeometry(0.46, 20), new THREE.MeshBasicMaterial({ color: 0x0B0D10 }));
    hole.rotation.x = -Math.PI / 2; hole.position.set(-1.5, 0.036, hatchZ); group.add(hole);
    const rim = new THREE.Mesh(new THREE.RingGeometry(0.46, 0.6, 20), sceneryMat(0x4A4F55));
    rim.rotation.x = -Math.PI / 2; rim.position.set(-1.5, 0.038, hatchZ); group.add(rim);
    const lid = new THREE.Mesh(new THREE.CylinderGeometry(0.5, 0.5, 0.05, 20), sceneryMat(0x3E434A));
    lid.position.set(-0.55, 0.06, hatchZ + 0.9); lid.rotation.set(0.06, 0, 0.04); group.add(lid); // resting on the patch, not sunk into it
    // Asphalt heap and a wheelbarrow at the head of the patch.
    const heap = new THREE.Mesh(new THREE.SphereGeometry(0.75, 9, 6), sceneryMat(0x1F2328));
    heap.scale.set(1, 0.42, 1.3); heap.position.set(-3.1, 0.02, workZ + 3.2); group.add(heap);
    const barrow = new THREE.Group();
    const tray = new THREE.Mesh(new THREE.BoxGeometry(0.6, 0.3, 0.9), sceneryMat(0x2F7D4F)); tray.position.y = 0.5; barrow.add(tray);
    const wheel = new THREE.Mesh(new THREE.CylinderGeometry(0.18, 0.18, 0.08, 10), sceneryMat(0x23282D));
    wheel.rotation.z = Math.PI / 2; wheel.position.set(0, 0.18, 0.55); barrow.add(wheel);
    [-0.22, 0.22].forEach(x => { const h = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.05, 0.9), sceneryMat(0x5B646A)); h.position.set(x, 0.55, -0.7); barrow.add(h); });
    barrow.position.set(-0.9, 0, workZ + 3.6); barrow.rotation.y = 0.5; group.add(barrow);
    // The hatch is fenced by four cones; the zone ends with a closing cone line.
    [[-0.8, -0.8], [0.8, -0.8], [-0.8, 0.8], [0.8, 0.8]].forEach(([dx, dz]) => {
      const cone = createTrafficCone(); cone.position.set(-1.5 + dx, 0, hatchZ + dz); group.add(cone); prop(cone, 0.2, 'cone');
    });
    for (let i = 0; i < 3; i++) {
      const cone = createTrafficCone(); cone.position.set(-0.3 - i * 1.1, 0, workZ + 15 + i * 1.5); group.add(cone); prop(cone, 0.2, 'cone');
    }
    // Crew: a worker with a rake on the patch (a real participant: hitting
    // him is a collision) and one down the hatch, head and shoulders out.
    const vest = '#F97316';
    const raker = addRoadActor(group, { id: 'road_worker', type: 'pedestrian', name: 'Рабочий', color: vest, worker: true },
      new THREE.Vector3(-2.7, 0.03, workZ + 6.5), Math.PI / 2 - 0.3,
      [new THREE.Vector3(-2.7, 0.03, workZ + 6.5), new THREE.Vector3(-2.7, 0.03, workZ + 6.51)], 0);
    raker.mesh.userData.badge.visible = false;
    dressWorker(raker.mesh, 'rake');
    ev.actors.push(raker);
    const digger = createPedestrian(0xF97316, 4);
    dressWorker(digger, 'shovel');
    digger.position.set(-1.5, -0.78, hatchZ); digger.rotation.y = -Math.PI / 2;
    // Standing below the road: the asphalt hides everything under the hole.
    group.add(digger);
    state.crews.push({ ev, raker, digger, hatch: new THREE.Vector3(-1.5, 0, hatchZ), group, t: Math.random() * 5, duck: 0 });
    return ev;
  }

  // Hard hat and a long-handled tool held in both hands.
  function dressWorker(person, tool) {
    const body = person.userData.body || person;
    const hat = new THREE.Mesh(new THREE.SphereGeometry(0.21, 10, 5, 0, Math.PI * 2, 0, Math.PI / 2), sceneryMat(0xFACC15));
    hat.position.set(0, 1.42, 0); body.add(hat);
    const brim = new THREE.Mesh(new THREE.CylinderGeometry(0.25, 0.25, 0.03, 12), sceneryMat(0xFACC15));
    brim.position.set(0, 1.43, 0.03); body.add(brim);
    const stripe = new THREE.Mesh(new THREE.BoxGeometry(0.44, 0.06, 0.28), sceneryMat(0xE5E7EB));
    stripe.position.set(0, 0.86, 0); body.add(stripe);
    const arm = person.userData.arms?.[1];
    if (!arm) return;
    const handle = new THREE.Mesh(new THREE.CylinderGeometry(0.025, 0.025, 1.3, 6), sceneryMat(0x9A7B55));
    handle.rotation.x = Math.PI / 2 - 0.5; handle.position.set(0, -0.42, 0.5); arm.add(handle);
    const head = new THREE.Mesh(tool === 'rake' ? new THREE.BoxGeometry(0.5, 0.05, 0.08) : new THREE.BoxGeometry(0.24, 0.03, 0.3),
      sceneryMat(tool === 'rake' ? 0x6B7280 : 0x9CA3AF));
    head.position.set(0, -0.72, 1.06); arm.add(head);
    person.userData.tool = tool;
  }

  // Idle work loops for the road crews; a worker never walks into traffic.
  function updateCrews(dt) {
    state.crews = (state.crews || []).filter(c => c.group.parent);
    const p = playerCarGroup.position;
    state.crews.forEach(c => {
      c.t += dt;
      const r = c.raker;
      if (!r.fall && !r.done) {
        // Raking: long strokes towards himself, a slight lean with each one.
        const stroke = Math.sin(c.t * 2.4);
        r.mesh.userData.arms.forEach((arm, i) => { arm.rotation.x = -0.55 + stroke * 0.35 + i * 0.1; });
        r.mesh.userData.body.rotation.x = 0.12 + stroke * 0.06;
      }
      // Down the hatch: digging strokes; ducks when a car comes too close.
      const d = c.digger;
      const hatchWorld = c.group.localToWorld(c.hatch.clone());
      const near = hatchWorld.distanceTo(p) < 5 && Math.abs(state.speed) > 0.5;
      c.duck = Math.max(0, Math.min(1, c.duck + (near ? 3 : -0.8) * dt));
      const lift = Math.max(0, Math.sin(c.t * 1.7)) * 0.08;
      d.position.y = -0.78 + lift - c.duck * 0.75;
      d.userData.arms.forEach((arm, i) => { arm.rotation.x = -1.0 + Math.sin(c.t * 3.1 + i * 0.4) * 0.45; });
    });
  }

  // Loose roadside props (cones, barrier parts): knocked flying by the
  // player's car, they tumble, bounce and settle on the ground.
  function knockProp(prop) {
    const speed = Math.abs(state.speed);
    const sign = Math.sign(state.speed) || 1;
    const fwd = new THREE.Vector3(Math.sin(playerCarGroup.rotation.y), 0, Math.cos(playerCarGroup.rotation.y)).multiplyScalar(sign);
    const parts = prop.kind === 'barrier' ? [...prop.mesh.userData.parts] : [prop.mesh];
    const parent = prop.mesh.parent;
    parts.forEach((part, i) => {
      if (part !== prop.mesh) parent.attach(part); // keep the world pose, fly on its own
      const at = part.getWorldPosition(new THREE.Vector3());
      const side = new THREE.Vector3(fwd.z, 0, -fwd.x).multiplyScalar(
        Math.sign(at.clone().sub(playerCarGroup.position).dot(new THREE.Vector3(fwd.z, 0, -fwd.x))) || (i % 2 ? 1 : -1));
      const light = prop.kind === 'cone';
      const v = fwd.clone().multiplyScalar(speed * (light ? 1.25 : 0.9) + 0.8)
        .addScaledVector(side, (light ? 1.6 : 1.1) + Math.random() * 1.4 + speed * 0.12);
      v.y = (light ? 2.4 : 1.6) + speed * (light ? 0.22 : 0.14) + Math.random();
      state.flying.push({ mesh: part, v, spin: new THREE.Vector3(Math.random() - 0.5, Math.random() - 0.5, Math.random() - 0.5)
        .normalize().multiplyScalar(6 + speed * 0.6), rest: light ? 0.16 : 0.04, settled: false });
    });
    if (prop.kind === 'barrier') parent.remove(prop.mesh);
    prop.knocked = true;
    state.speed *= prop.kind === 'barrier' ? 0.6 : 0.93;
    gameAudio?.scrapeHit();
    const ev = prop.ev;
    if (ev && prop.penalize !== false && !ev.propPenalized && !state.attract) {
      ev.propPenalized = true;
      roadViolation('roadworks');
    }
  }

  function updateProps(dt) {
    state.props = (state.props || []).filter(pr => !pr.knocked && pr.mesh.parent && pr.root.parent);
    state.flying = (state.flying || []).filter(f => f.mesh.parent);
    if (Math.abs(state.speed) > 0.3) {
      const player = playerFootprint();
      for (const pr of state.props) {
        const world = pr.mesh.getWorldPosition(new THREE.Vector3());
        if (world.distanceTo(player.p) > 6) continue;
        pr.probe ??= clipProbe(pr.mesh);
        if (clippedAway(pr.probe?.material, world)) continue;
        const yaw = pr.mesh.getWorldQuaternion(new THREE.Quaternion());
        const box = { p: world, yaw: new THREE.Euler().setFromQuaternion(yaw, 'YXZ').y,
          halfWidth: pr.radius, halfLength: pr.depth ?? pr.radius };
        if (footprintsOverlap(player, box, 0.02)) knockProp(pr);
      }
    }
    for (const f of state.flying) {
      if (f.settled) continue;
      const parent = f.mesh.parent;
      const world = f.mesh.getWorldPosition(new THREE.Vector3());
      f.v.y -= 9.8 * dt;
      world.addScaledVector(f.v, dt);
      f.mesh.rotateOnAxis(f.spin.clone().normalize(), f.spin.length() * dt);
      if (world.y <= f.rest && f.v.y < 0) {
        world.y = f.rest;
        f.v.y = -f.v.y * 0.3;
        f.v.x *= 0.55; f.v.z *= 0.55;
        f.spin.multiplyScalar(0.5);
        if (f.v.length() < 0.9) {
          // Come to rest lying on the side, keeping the direction it slid in.
          f.settled = true;
          f.mesh.rotation.set(Math.PI / 2, 0, Math.random() * Math.PI * 2);
        }
      }
      f.mesh.position.copy(parent.worldToLocal(world));
    }
  }

  // Lane blockages other traffic must drive round, in the group's own
  // coordinates (road events are rebased with the world).
  function addBlocker(group, x0, x1, z0, z1) {
    state.blockers = (state.blockers || []).filter(b => b.group.parent);
    state.blockers.push({ group, x0, x1, z0, z1 });
  }

  function pointBlocked(p, self) {
    for (const b of state.blockers || []) {
      if (!b.group.parent) continue;
      b.probe ??= clipProbe(b.group);
      if (clippedAway(b.probe?.material, p)) continue;
      const l = b.group.worldToLocal(p.clone());
      if (l.x >= b.x0 && l.x <= b.x1 && l.z >= b.z0 && l.z <= b.z1) return true;
    }
    // A car left standing after a crash (or broken down) blocks its lane too.
    for (const o of state.actors) {
      if (o === self || o.done || !(o.crashed || o.config.id === 'road_obstacle_car')) continue;
      const f = actorFootprint(o), d = p.clone().sub(f.p);
      const along = Math.abs(d.x * Math.sin(f.yaw) + d.z * Math.cos(f.yaw));
      const across = Math.abs(d.x * Math.cos(f.yaw) - d.z * Math.sin(f.yaw));
      if (along < f.halfLength + 1.5 && across < f.halfWidth + 1.1) return true;
    }
    return false;
  }

  // Every moving vehicle keeps its route but steps out into the next lane
  // round anything standing in its own one, and back in once past.
  function applyDetour(a, travelled) {
    if (['pedestrian'].includes(a.config.type) || a.crashed || a.config.id === 'road_obstacle_car') return;
    if (!state.blockers?.length && !state.actors.some(o => o.crashed || o.config.id === 'road_obstacle_car')) {
      if (!a.detour) return;
    }
    const parent = a.mesh.parent;
    const world = a.mesh.getWorldPosition(new THREE.Vector3());
    const fwd = new THREE.Vector3(0, 0, 1).applyQuaternion(a.mesh.getWorldQuaternion(new THREE.Quaternion()));
    fwd.y = 0; fwd.normalize();
    const left = new THREE.Vector3(fwd.z, 0, -fwd.x);
    let blocked = false;
    for (let d = -5; d <= 24 && !blocked; d += 1.5) blocked = pointBlocked(world.clone().addScaledVector(fwd, d), a);
    if (blocked && !a.detourSide) {
      // Towards whichever side has road: normally the next lane on the left.
      const probe = side => world.clone().addScaledVector(left, 3.6 * side).addScaledVector(fwd, 8);
      a.detourSide = roadSupports(probe(1)) && !pointBlocked(probe(1), a) ? 1 : -1;
    }
    const want = blocked ? 3.6 * a.detourSide : 0;
    const prev = a.detour || 0;
    const next = prev + THREE.MathUtils.clamp(want - prev, -0.35 * travelled, 0.35 * travelled);
    a.detour = Math.abs(next) < 1e-3 && !blocked ? 0 : next;
    if (!a.detour && !blocked) a.detourSide = 0;
    if (!a.detour) return;
    const leftLocal = left.clone();
    if (parent) {
      const q = parent.getWorldQuaternion(new THREE.Quaternion()).invert();
      leftLocal.applyQuaternion(q);
    }
    a.mesh.position.addScaledVector(leftLocal, a.detour);
    a.mesh.rotation.y += Math.atan2(next - prev, Math.max(travelled, 1e-3));
  }

  function buildObstacleEvent(group, obstZ) {
    const ev = { group, kind: 'obstacle', obstZ, phase: 'approach', actors: [] };
    addBlocker(group, -3.2, -0.4, obstZ - 15.5, obstZ + 3);
    // A real, solid participant (it used to be scenery the player drove
    // through), standing with its hazard lights on.
    const at = new THREE.Vector3(-1.8, 0, obstZ);
    const broken = addRoadActor(group, { id: 'road_obstacle_car', type: 'car', color: '#64748B', name: 'Сломанное авто' },
      at, 0, [at, at.clone().add(new THREE.Vector3(0, 0, 0.01))], 0);
    broken.mesh.userData.blinkerSide = 'hazard';
    ev.actors.push(broken);
    const mechanic=new THREE.Group();mechanic.userData.changingTyre=true;
    modelBox(mechanic,[.42,.5,.28],0x2E618B,0,.67,0);
    modelPart(mechanic,new THREE.SphereGeometry(.17,10,8),0xD9AD87,0,.99,.1);
    for(const side of [-1,1]) {
      modelBox(mechanic,[.16,.18,.48],0x343B47,side*.13,.15,-.03);
      modelBox(mechanic,[.15,.35,.17],0x343B47,side*.13,.34,.15);
      const arm=modelBox(mechanic,[.13,.46,.14],0x2E618B,side*.26,.55,.17);arm.rotation.x=-.7;
      modelBox(mechanic,[.11,.11,.13],0xD9AD87,side*.26,.35,.33);
    }
    mergeModelParts(mechanic);mechanic.position.set(-3.55,.02,obstZ+1.25);mechanic.rotation.y=Math.PI/2;group.add(mechanic);
    const wheel=new THREE.Mesh(new THREE.TorusGeometry(.27,.105,8,16),new THREE.MeshLambertMaterial({color:0x202328}));
    wheel.rotation.x=Math.PI/2;wheel.position.set(-3.7,.12,obstZ+.25);wheel.userData.spareWheel=true;group.add(wheel);

    const triangle = createEmergencyTriangle();
    triangle.position.set(-1.8, 0, obstZ - 15);
    group.add(triangle);
    state.props.push({ mesh: triangle, radius: 0.55, kind: 'cone', ev, root: group, penalize: false });
    return ev;
  }

  function buildCourtyardEvent(group, yardZ) {
    const ev = { group, kind: 'courtyard', yardZ, phase: 'approach', actors: [] };
    const asphalt = new THREE.MeshLambertMaterial({ color: BRAND.asphalt });
    // The driveway runs out of the yard and across the pavement (a lowered
    // kerb); lamps, trees and fences in its way are cleared.
    clearRoadside(yardZ, 6, -17, -4.3);
    // A garage by the road: the car comes out of its open door, over a
    // concrete apron and a lowered kerb.
    const concrete = new THREE.MeshLambertMaterial({ color: 0xA7ADB2 });
    addFlatPlane(group, 3.9, 3.6, -9.35, yardZ, 0.02, concrete.clone());   // apron
    // Lowered kerb: from the pavement's outer edge right up to the kerb
    // (the pavement starts just inside 4.2), no strip of pavement left.
    ev.driveway=replaceCorridorStrip(yardZ-5,yardZ+5,g=>{
      roadSurface(g,8.4,10+SEAM,0,yardZ);
      const zs=[];for(let q=yardZ-5;q<=yardZ+5;q+=.25)zs.push(q);
      const ramp=new THREE.BufferGeometry(),positions=[],indices=[];
      for(const q of zs){const height=.02+.16*THREE.MathUtils.smoothstep(Math.abs(q-yardZ),1.8,4.8);positions.push(-7.4,height,q,-4.2,height,q);}
      for(let i=0;i<zs.length-1;i++){const a=2*i;indices.push(a,a+2,a+1,a+1,a+2,a+3);}
      ramp.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));ramp.setIndex(indices);ramp.computeVertexNormals();
      const mesh=new THREE.Mesh(ramp,concrete.clone());mesh.userData.loweredDriveway=true;g.add(mesh);
      roadSurface(g,3.2,10,5.8,yardZ,true);
      const paint=roadMarkingMat();for(let q=yardZ-5;q<yardZ+5;q+=5)addFlatPlane(g,.13,2,0,q,.028,paint);
    });
    addFlatPlane(group,3.4,3.6,-5.7,yardZ,.021,concrete);
    const wall = sceneryMat(0xC9B89E), roofMat = sceneryMat(0x7A5A48), dark = sceneryMat(0x22262A);
    const box = (w, h, d, x, y, z, m) => { const b = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), m); b.position.set(x, y, z); b.castShadow = true; group.add(b); return b; };
    box(6.2, 2.5, 0.2, -14.4, 1.25, yardZ - 1.75, wall);  // side walls
    box(6.2, 2.5, 0.2, -14.4, 1.25, yardZ + 1.75, wall);
    box(0.2, 2.5, 3.7, -17.4, 1.25, yardZ, wall);         // back wall
    box(0.2, 0.5, 3.7, -11.35, 2.25, yardZ, wall);        // lintel over the door
    box(6.6, 0.18, 4.1, -14.4, 2.6, yardZ, roofMat);      // roof
    addFlatPlane(group, 6, 3.3, -14.4, yardZ, 0.021, dark); // shaded floor inside
    const door = box(0.08, 0.5, 3.3, -11.3, 2.1, yardZ, sceneryMat(0x8A96A0)); // rolled-up door
    door.rotation.z = 0.2;

    // Pulls up to the road edge with its right signal on, waits for the
    // player to pass (they have priority, 8.3), then turns right after them.
    const V = (x, z) => new THREE.Vector3(x, 0, z);
    const start = V(-14.2, yardZ);
    const cfg = { id: 'road_yard_car', type: 'car', name: 'Авто из двора', color: '#3B82F6' };
    const car = addRoadActor(group, cfg, start, Math.PI / 2, [start, V(-4.9, yardZ), V(-3.2, yardZ + 1.2),
      V(-2.0, yardZ + 4.5), V(-1.8, yardZ + 12), V(-1.8, yardZ + 260)], 7);
    car.stopAtDistance = 8.0; // nose at the kerb, not over the edge line
    car.stopFor = Infinity;
    car.signalPlan = [{ from: 0, to: 14, side: 'right' }];
    ev.actors.push(car);
    return ev;
  }

  function buildCyclistEvent(group, cycZ) {
    const ev = { group, kind: 'cyclist', cycZ, phase: 'approach', actors: [] };
    const start = new THREE.Vector3(-3.4, 0, cycZ);
    const cfg = { id: 'road_free_cyclist', type: 'cyclist', name: 'Велосипедист', color: '#10B981' };
    const cyc = addRoadActor(group, cfg, start, 0, [
      start,
      new THREE.Vector3(-3.4, 0, cycZ + 80),
      new THREE.Vector3(-3.4, 0, cycZ + 250)
    ], 4.2);
    cyc.waitsForPlayer = false;
    ev.actors.push(cyc);
    return ev;
  }

  function buildEmergencyEvent(group, emZ) {
    const ev = { group, kind: 'emergency', emZ, phase: 'approach', actors: [] };
    const start = new THREE.Vector3(1.8, 0, emZ + 120);
    const cfg = { id: 'road_emergency_car', type: 'special', name: 'Спецмашина', color: '#0574F8', beacon: 'blue', siren: true };
    const sp = addRoadActor(group, cfg, start, Math.PI, [
      start,
      new THREE.Vector3(1.8, 0, emZ - 30),
      new THREE.Vector3(1.8, 0, emZ - 180)
    ], 14.0);
    sp.waitsForPlayer = false;
    ev.actors.push(sp);
    return ev;
  }

  function roadEventLimit(z, limit) {
    const ev = state.roadEvent;
    if (!ev || ev.phase !== 'approach' || ev.stopZ === undefined) return limit;
    const distance = ev.stopZ - z;
    if (distance + 3 <= 0) return limit;
    return Math.min(limit, Math.sqrt(Math.max(0, 2 * 8 * distance)));
  }

  function startRoadQuestion() {
    const ev = state.roadEvent;
    if (ev.kind === 'emergency_lane') {
      const car = ev.police, gap = playerCarGroup.position.z - car.mesh.position.z;
      // The inspector jumps directly to the question instead of driving the
      // approach. Keep its layout identical to a police car catching up.
      if (gap > 24 || gap < 10) {
        car.mesh.position.set(-1.8,0,playerCarGroup.position.z-10);
        car.initialPos.copy(car.mesh.position);
        car.path=curve([car.mesh.position.clone(),new THREE.Vector3(-1.8,0,ev.stopZ+320)]);
        car.length=car.path.getLength();car.distance=0;
      }
      car.stopAtDistance=car.distance;car.stopFor=Infinity;car.speed=0;car.maxSpeed=18;
    }
    ev.phase = 'question';
    if (ev.guide) ev.guide.visible = true;
    (ev.joiners || []).forEach(join => join());
    ev.joiners = null;
    state.speed = 0; state.isAccelerating = false; state.steering = 0; state.laneChangeX = null; state.autoPath = null;
    state.isAtSituation = true;
    sendToFlutter({ event: 'approach_situation', situation: ev.situation });
  }

  function releaseRoadActors(ev) { ev.actors.forEach(a => { a.waitsForPlayer = false; }); }

  // Once the question is answered its participants lose their badges.
  function hideBadges(actors) { actors.forEach(a => { if (a.mesh.userData.badge) a.mesh.userData.badge.visible = false; }); }
  function startRoadManual() {
    const ev = state.roadEvent;
    resetQuestionCamera();
    ev.phase = 'manual';
    ev.lanePrevious = playerCarGroup.position.clone();
    if (ev.scene.playerLane === 'left') playerCarGroup.position.x = -1.8;
    if (ev.guide) ev.guide.visible = false;
    hideBadges(ev.actors);
    ev.actors.forEach(a => { if (a.stopFor === Infinity && a.config.maneuver === 'overtake') a.stopFor = 0; });
    releaseRoadActors(ev);
    if (ev.kind === 'overtake' && !ev.scene.overtake) {
      // Overtaking is forbidden here: the vehicle ahead does not make the
      // player crawl behind it — it speeds up and drives away.
      ev.actors.forEach(a => {
        if (a.config.maneuver || a.config.approach === 'right' || a.config.approach === 'oncoming') return;
        a.maxSpeed = Math.max(a.maxSpeed, 24); a.speedAway = true;
      });
    }
    state.isAtSituation = false;
    state.isResolvingSituation = false;
    state.speed = 0;
  }

  function finishRoadEvent(cleared = true) {
    const ev = state.roadEvent;
    if (!ev) return;
    const id = ev.situation?.id;
    releaseRoadActors(ev);
    ev.phase = 'done';
    state.roadEvent = null;
    state.isAtSituation = false;
    if (cleared && id) sendToFlutter({ event: 'situation_cleared', situationId: id });
  }

  // Called when the world is about to be rebuilt behind the player (U-turn).
  function cancelRoadEvent() {
    const ev = state.roadEvent;
    if (!ev) return;
    finishRoadEvent(ev.phase === 'manual' || ev.phase === 'question');
  }

  function roadOvertakeAllowedAt(z) {
    const ev = state.roadEvent;
    // Detouring a closed lane (4.2.2) or a stopped car uses the oncoming lane
    // legally (11.7 governs who gives way); only over its length.
    if (ev?.kind === 'roadworks' && z >= ev.workZ - 34 && z <= ev.zoneEnd + 10) return true;
    if (ev?.kind === 'obstacle' && z >= ev.obstZ - 20 && z <= ev.obstZ + 12) return true;
    if (ev?.scene?.wideCity && z >= ev.cityFrom && z <= ev.cityTo) return false; // both own lanes have negative X
    if (ev?.kind === 'temporary_bypass' && playerCarGroup.position.x > 0 && playerCarGroup.position.x < 6.2 && z >= ev.bypassFrom && z <= ev.bypassTo) return true;
    if (ev?.kind === 'detour' && z >= ev.obstZ - 30 && z <= ev.obstZ + 12) return true;
    // Overtaking a cyclist on a broken centre line is legal; the lane is
    // used only alongside them.
    if (ev?.kind === 'cyclist') {
      const bike = ev.actors[0];
      if (bike && !bike.done && Math.abs(bike.mesh.getWorldPosition(new THREE.Vector3()).z - z) < 16) return true;
    }
    // Both lanes of the own carriageway are the player's; the opposite
    // carriageway beyond the median is not.
    if (ev?.scene?.motorway && z >= ev.motorwayFrom && z <= ev.motorwayTo && Math.cos(playerCarGroup.rotation.y) > 0 &&
        playerCarGroup.position.x < 4.3) return true;
    if (!ev || ev.phase !== 'manual' || ev.kind !== 'overtake') return false;
    const o = ev.scene.overtake;
    if (ev.scene.junction?.priority === 'equal') return z >= ev.startZ - 12 && z <= ev.endZ && Math.abs(z - ev.junctionZ) > 8;
    if (ev.scene.vehicles?.some(v => v.alreadyOvertaking || v.joinsAtQuestion)) return z >= ev.startZ - 12 && z <= ev.endZ &&
      ev.actors.filter(a => a.config.maneuver === 'overtake').every(a => a.distance > (a.passedAt || 90));
    if (o === true) return z >= ev.startZ - 12 && z <= ev.endZ;
    if (o === 'before_intersection') return z >= ev.startZ - 12 && z < ev.laneDeadlineZ;
    // After the crossing only: before it the solid line of 1.11 is on the
    // player's side, on it overtaking is banned (11.4).
    if (o === 'after_crosswalk') return z > ev.crosswalkZ + 6 && z <= ev.endZ;
    // 11.4: no overtaking on a railway crossing or closer than 100 m before
    // it — finished before that point (10.11), or started once past it
    // (17.11, 21.11: the boundary is the signal posts just after the track).
    if (o === 'before_crossing') return z >= ev.startZ - 12 && z < ev.crossingZ - 100;
    if (o === 'after_crossing') return z > ev.crossingZ + 4.6 && z <= ev.endZ;
    return false;
  }

  // The limit in force: a sign from a speed question, else the built-up 60.
  function effectiveLimitKmH() { return state.speedLimitKmH || state.baseLimitKmH; }
  function roadViolation(type) {
    highlightMistake({ type });
    sendToFlutter({ event: 'violation', type, episode: ++state.violationEpisode });
  }

  function updateRoadEvent(dt) {
    updateProps(dt);
    updateCrews(dt);
    const ev = state.roadEvent;
    // Simulated time, so signals freeze on pause and stay deterministic in tests.
    state.signalClock = (state.signalClock || 0) + dt;
    const now = state.signalClock * 1000;
    // Parked junction traffic (not yet released) signals too: use the
    // situation's motions when they exist, else the static config side.
    const parked = state.intersections.flatMap(it => it.motions ? [] : it.actors.map(a => ({ mesh: a.mesh, distance: 0,
      signalPlan: a.config.targetAction === 'turn_right' ? [{ from: 0, to: 1, side: 'right' }] :
        (a.config.targetAction === 'turn_left' || a.config.targetAction === 'uturn') ? [{ from: 0, to: 1, side: 'left' }] : null })));
    [...state.actors, ...parked].forEach(a => {
      const lamps = a.mesh.userData.blinkerLamps;
      if (!lamps) return;
      const planned = a.signalPlan ? a.signalPlan.find(p => a.distance >= p.from && a.distance < p.to)?.side || null
        : a.mesh.userData.blinkerSide;
      const on = Math.floor(now / 380) % 2 === 0;
      lamps.left.forEach(l => { l.visible = on && (planned === 'left' || planned === 'hazard'); });
      lamps.right.forEach(l => { l.visible = on && (planned === 'right' || planned === 'hazard'); });
    });
    // The car can always exceed the limit (that is what a violation is); its
    // top speed only rises where a higher limit allows it: 65 km/h in town,
    // up to 120 past a motorway sign. Over the limit by 5+ km/h for 0.8 s is
    // a violation.
    if (state.carriedZoneEndZ !== undefined && playerCarGroup.position.z > state.carriedZoneEndZ) { state.speedLimitKmH = null; state.speedZoneActive = false; state.carriedZoneEndZ = undefined; }
    const limit = effectiveLimitKmH();
    state.maxSpeed = Math.min(33, limit / 3.6);
    {
      const over = state.speed * 3.6 > limit + 5;
      state.speedingTime = over ? (state.speedingTime || 0) + dt : 0;
      if (!over) state.speedingPenalized = false;
      if (over && state.speedingTime > 0.8 && !state.speedingPenalized) {
        state.speedingPenalized = true;
        roadViolation('speeding');
      }
    }
    const z = playerCarGroup.position.z, x = playerCarGroup.position.x;
    // A side exit from an authored crossing becomes the next driving corridor,
    // just like an exit from a ticket junction. Never strand the player at the
    // end of a decorative cross street (their previews end after 200 m).
    const sj = state.sideJunction;
    if (sj && !state.resolution && Math.abs(x) > 24 && Math.abs(z - sj.junctionZ) < (Math.abs(x) > 40 ? 6 : 4.3)) {
      const heading = Math.sign(x) * Math.PI / 2;
      const error = Math.atan2(Math.sin(playerCarGroup.rotation.y - heading), Math.cos(playerCarGroup.rotation.y - heading));
      if (Math.abs(error) < (Math.abs(x) > 40 ? Math.PI / 2 : 0.7)) {
        const direction = x < 0 ? 'right' : 'left';
        if (ev) finishRoadEvent(false);
        state.sideJunction = null;
        state.resolution = {
          motions: sj.actors, yielding: [], exitDirection: direction, exitYaw: heading,
          spec: { maneuver: direction },
          intersection: { situation: sj.situation, centerZ: sj.junctionZ,
            guide: new THREE.Group(), previews: sj.previews },
        };
        finishManeuver();
        return;
      }
    }
    if (!ev) return;
    if (ev.kind === 'busstop') {
      const bus = ev.actors[0];
      if (ev.phase === 'approach' && z > ev.bayZ - 120) { ev.phase = 'manual'; releaseRoadActors(ev); }
      if (bus && !bus.done && bus.stopAtDistance !== undefined) {
        // Doors close and it signals out a moment after the player comes near.
        if (z > ev.bayZ - 35 && bus.stopFor > 1.8) bus.stopFor = 1.8;
        bus.signalPlan = bus.stopFor > 0 ? (z > ev.bayZ - 35 ? [{ from: 0, to: 30, side: 'left' }] : null) : [{ from: 0, to: 30, side: 'left' }];
        if (bus.distance >= bus.stopAtDistance && bus.stopFor > 0) {
          // Dwell with the doors open, then merge back at full speed.
          bus.stopFor -= dt; bus.maxSpeed = 0; bus.speed = 0;
        } else if (bus.stopFor <= 0) bus.maxSpeed = 11;
      }
      if (z > ev.bayZ + 60 || z < ev.bayZ - 200) finishRoadEvent(false);
      return;
    }
    if (ev.kind === 'crosswalk') {
      const ped = ev.pedestrian;
      if (ev.phase === 'approach' && z > ev.crosswalkZ - 58 && z < ev.crosswalkZ - 6) { ev.phase = 'manual'; releaseRoadActors(ev); }
      const front = z + playerCarGroup.userData.halfLength;
      if (ev.phase === 'manual' && ev.passedZ === null && front >= ev.crosswalkZ - 2.4) {
        ev.passedZ = z;
        if (!ped.fall && !ped.done && Math.abs(ped.mesh.position.x) < 4.6 && Math.cos(playerCarGroup.rotation.y) > 0.5) roadViolation('pedestrian');
      }
      if (z > ev.crosswalkZ + 8 || z < ev.crosswalkZ - 120) finishRoadEvent(false);
      return;
    }
    if (['roadworks', 'obstacle', 'courtyard', 'cyclist', 'emergency'].includes(ev.kind)) {
      const markZ = ev.workZ || ev.obstZ || ev.yardZ || ev.cycZ || ev.emZ || 0;
      // The yard car goes once the player has passed the driveway.
      if (ev.kind === 'courtyard') ev.actors.forEach(a => { if (a.stopFor === Infinity && z > ev.yardZ + 9) a.stopFor = 0.8; });
      if (ev.phase === 'approach' && z > markZ - 50) {
        ev.phase = 'manual';
        releaseRoadActors(ev);
      }
      if (z > markZ + 50 || z < markZ - 120) finishRoadEvent(false);
      return;
    }
    if (ev.rail) updateRailway(ev, dt, z, x);
    if (ev.phase === 'approach' && z > ev.stopZ + 6) {
      // The stop was skipped (e.g. after a collision push); ask no question here.
      finishRoadEvent(false);
      return;
    }
    if (ev.phase !== 'manual') return;
    checkRoadLaneRules(ev);
    if (ev.kind === 'speed' && z > ev.signZ) { state.speedLimitKmH = ev.scene.limitKmH; state.speedZoneActive = !!ev.scene.speedZone; }
    if (ev.requiredStopZ !== undefined) checkRequiredStop(ev, ev.requiredStopZ, dt, roadViolation);
    if (ev.kind === 'bus_departure') updateQuestionBus(ev, dt);
    if (ev.kind === 'emergency_lane') updateQuestionPolice(ev, dt);
    if (ev.kind === 'temporary_bypass') updateTemporaryBypass(ev);
    if (ev.kind === 'speed' && ev.endSignZ !== undefined && z > ev.endSignZ) { state.speedLimitKmH = null; state.speedZoneActive = false; }
    // Vehicles ahead leave the scene once the stretch is over so that they
    // never block the next junction or its question.
    // A slow vehicle the player may only overtake before a point (a railway
    // crossing, a junction) does not crawl on past it: the chance is gone.
    const o = ev.scene.overtake;
    const windowEnd = o === 'before_crossing' ? ev.crossingZ - 100 : o === 'before_intersection' && ev.junctionZ ? ev.junctionZ - 8 : Infinity;
    ev.actors.forEach(a => {
      if (a.config.type === 'train') return;
      if (a.holdSpeedUntil !== undefined ? a.distance > a.holdSpeedUntil :
          (a.config.name !== 'Встречный' && a.mesh.position.z > Math.min(ev.endZ - 15, windowEnd))) {
        if (!a.speedAway) a.maxSpeed = Math.min(state.maxSpeed, { cart: 7, tractor: 11 }[a.config.type] || Infinity);
      }
    });
    if (ev.kind === 'overtake') {
      const oncomingLane = Math.cos(playerCarGroup.rotation.y) * x > 0.85;
      const forbiddenHere = oncomingLane && z >= ev.startZ - 12 && z <= ev.endZ && !roadOvertakeAllowedAt(z);
      if (forbiddenHere && !ev.overtakePenalized) { ev.overtakePenalized = true; roadViolation('overtaking'); }
      if (!oncomingLane) ev.overtakePenalized = false;
    }
    if (ev.scene.junction && !ev.priorityPenalized && z + playerCarGroup.userData.halfLength > ev.junctionZ - 4.2 &&
        ev.actors.some(a => a.config.approach === 'right' && !a.cleared)) {
      ev.priorityPenalized = true; roadViolation('priority');
    }
    if (z > ev.endZ || z < ev.startZ - 45) finishRoadEvent(true);
  }

  // The crossing's signals always run; with a barrier (2.16) the train comes
  // through once the question is answered, then the booms rise and the
  // queue moves off. Until then (15.3) going round the waiting vehicles
  // through the oncoming lane, or past the boom, is a railway fault.
  function updateRailway(ev, dt, z, x) {
    const rail = ev.rail, r = ev.scene.railway;
    updateRailwaySignals(rail);
    if (ev.phase !== 'manual') return;
    rail.elapsed = (rail.elapsed || 0) + dt;
    if (r.requireStop) checkRequiredStop(ev, ev.railBoundaryZ, dt, roadViolation);
    if (!rail.open && rail.elapsed >= 3 && (!r.train || rail.train.distance > rail.train.clearCrossingDistance)) {
      rail.lift = Math.min(1, rail.lift + dt / 2.5);
      setRailwayBooms(rail);
      if (rail.lift >= 1) {
        rail.open = true;
        ev.actors.forEach(a => { if (a.stopFor === Infinity) a.stopFor = 0; });
      }
    }
    if (rail.open) return;
    const oncomingLane = Math.cos(playerCarGroup.rotation.y) * x > 0.85;
    const pastBoom = z + playerCarGroup.userData.halfLength > ev.railBoundaryZ + 0.25 && z < ev.crossingZ + 4 + ((r.tracks || 1) - 1) * 5;
    if ((oncomingLane && z > ev.startZ - 12 && z < ev.crossingZ + 4) || pastBoom) {
      if (!ev.railPenalized) { ev.railPenalized = true; roadViolation('railway'); }
    } else ev.railPenalized = false;
  }

  // --- Weather: clear / overcast / rain, changing every minute or two ---
  // state.rain (0..1) and state.overcast (0..1) blend sky, fog, light, the
  // wet look of the asphalt and the rain particles. No gameplay effect.
  let weatherFx = null;
  function pickWeather(previous) {
    const options = previous === 'rain' ? ['clear', 'overcast'] :
      previous === 'overcast' ? ['rain', 'rain', 'clear'] : ['overcast', 'overcast', 'rain', 'clear'];
    return options[Math.floor(Math.random() * options.length)];
  }
  function weatherDuration(kind) {
    return kind === 'rain' ? 45 + Math.random() * 50 : kind === 'overcast' ? 35 + Math.random() * 45 : 60 + Math.random() * 90;
  }
  function ensureWeatherFx() {
    if (weatherFx) return weatherFx;
    // Rain: short vertical streaks in a box that travels with the player.
    const count = state.lowEnd ? 350 : 900;
    const positions = new Float32Array(count * 2 * 3);
    const drops = [];
    for (let i = 0; i < count; i++) {
      drops.push({ x: (Math.random() - 0.5) * 60, y: Math.random() * 30, z: (Math.random() - 0.5) * 70, speed: 20 + Math.random() * 8, len: 0.5 + Math.random() * 0.5 });
    }
    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    const lines = new THREE.LineSegments(geometry, new THREE.LineBasicMaterial({ color: 0xDCE6F0, transparent: true, opacity: 0 }));
    lines.frustumCulled = false;
    scene.add(lines);
    // Puddles: soft dark ellipses on the road that appear with the rain.
    const puddleTexture = (() => {
      const canvas = document.createElement('canvas'); canvas.width = canvas.height = 64;
      const ctx = canvas.getContext('2d');
      const g = ctx.createRadialGradient(32, 32, 2, 32, 32, 32);
      g.addColorStop(0, 'rgba(120,140,165,0.55)'); g.addColorStop(0.7, 'rgba(120,140,165,0.3)'); g.addColorStop(1, 'rgba(120,140,165,0)');
      ctx.fillStyle = g; ctx.fillRect(0, 0, 64, 64);
      return new THREE.CanvasTexture(canvas);
    })();
    weatherFx = { lines, drops, count, puddleTexture, puddles: [] };
    return weatherFx;
  }
  function addPuddles(seg, startZ, length) {
    const fx = ensureWeatherFx();
    for (let z = startZ + 6 + Math.random() * 10; z < startZ + length - 6; z += 14 + Math.random() * 16) {
      const puddle = new THREE.Mesh(new THREE.PlaneGeometry(2.2 + Math.random() * 2, 1.2 + Math.random() * 1.2),
        new THREE.MeshBasicMaterial({ map: fx.puddleTexture, transparent: true, opacity: 0, depthWrite: false }));
      puddle.rotation.x = -Math.PI / 2; puddle.rotation.z = Math.random() * Math.PI;
      puddle.position.set((Math.random() - 0.5) * 6.4, 0.031, z);
      puddle.userData.puddle = true;
      seg.add(puddle);
    }
  }
  function applyWeather() {
    const rain = state.rain || 0, overcast = Math.max(state.overcast || 0, rain);
    // App theme affects Flutter overlays only. Weather and season own the world.
    const sn = season();
    const clearSky = new THREE.Color(sn.sky), greySky = new THREE.Color(0xC3CACF), rainSky = new THREE.Color(0xAEB6BD);
    scene.background.copy(clearSky).lerp(greySky, overcast).lerp(rainSky, rain);
    scene.fog.color.copy(scene.background);
    scene.fog.density = 0.007 + overcast * 0.002 + rain * 0.004;
    ambientLight.intensity = THREE.MathUtils.lerp(sn.ambient, sn.ambient - 0.06, overcast);
    dirLight.intensity = THREE.MathUtils.lerp(sn.sunIntensity, 0.18, overcast);
    dirLight.color.setHex(sn.sun).lerp(new THREE.Color(0xDDE4EC), overcast);
    if (!weatherFx) return;
    const snow = sn.precipitation === 'snow';
    weatherFx.lines.material.color.setHex(snow ? 0xFFFFFF : 0xDCE6F0);
    weatherFx.lines.material.opacity = rain * (snow ? 0.85 : 0.55);
    scene.traverse(o => {
      if (o.userData.puddle) o.material.opacity = rain * (snow ? 0.35 : 0.9);
      else if ((o.userData.surface === 'road' || o.material?.userData.asphalt) && o.material?.color) o.material.color.setHex(BRAND.asphalt).lerp(new THREE.Color(0x1F2228), rain * 0.8);
    });
  }
  function updateWeather(dt) {
    if (!state.sky) state.sky = { kind: 'clear', left: 70 + Math.random() * 80 };
    const w = state.sky;
    if (!state.weatherOverride && !state.firstRun) {
      w.left -= dt;
      if (w.left <= 0) { w.kind = pickWeather(w.kind); w.left = weatherDuration(w.kind); }
    }
    const targetRain = w.kind === 'rain' ? 1 : 0, targetOvercast = w.kind === 'clear' ? 0 : 1;
    const k = Math.min(1, dt * 0.35);
    const before = [state.rain || 0, state.overcast || 0];
    state.rain = before[0] + (targetRain - before[0]) * k;
    state.overcast = before[1] + (targetOvercast - before[1]) * k;
    if (Math.abs(state.rain - before[0]) + Math.abs(state.overcast - before[1]) > 0.0005 || state.weatherDirty) { applyWeather(); state.weatherDirty = false; }
    if (state.rain < 0.02) { if (weatherFx) weatherFx.lines.visible = false; return; }
    const fx = ensureWeatherFx();
    fx.lines.visible = true;
    const p = fx.lines.geometry.attributes.position.array;
    const cx = playerCarGroup.position.x, cz = playerCarGroup.position.z + 12;
    const snow = season().precipitation === 'snow';
    fx.drops.forEach((d, i) => {
      // Snow drifts down slowly and sways; rain falls fast with the wind.
      d.y -= (snow ? d.speed * 0.12 : d.speed) * dt; d.z -= (snow ? 1 : 4) * dt;
      if (snow) d.x += Math.sin(d.y * 0.8 + i) * 0.6 * dt;
      if (d.y < 0) { d.y = 28 + Math.random() * 4; d.x = (Math.random() - 0.5) * 60; d.z = (Math.random() - 0.5) * 70; }
      if (d.z < -35) d.z += 70;
      const o = i * 6;
      p[o] = cx + d.x; p[o + 1] = d.y; p[o + 2] = cz + d.z;
      const len = snow ? 0.16 : d.len;
      p[o + 3] = cx + d.x + (snow ? 0.12 : 0); p[o + 4] = d.y + len; p[o + 5] = cz + d.z + (snow ? 0 : 0.12);
    });
    fx.lines.geometry.attributes.position.needsUpdate = true;
  }

  // --- Attract mode (signed-out visitors): the city lives, the player waits ---
  // The engine keeps running; the player's car stays put while traffic
  // passes: oncoming cars, and cars from behind that swing round the parked
  // player. Spawns are spaced so that the two never meet beside the player.
  function updateAttract(dt) {
    if (!state.attract) return;
    state.speed = 0; state.isAccelerating = false; state.isBraking = false;
    state.attractClock = (state.attractClock || 0) + dt;
    if (state.attractClock < (state.attractNext ?? 2)) return;
    // Laid out along the road beside the player: the world is rebased so
    // travel is +Z, the right-hand lane sits at the driver's right (-X).
    const yaw = playerCarGroup.rotation.y;
    const fwd = new THREE.Vector3(Math.sin(yaw), 0, Math.cos(yaw));
    const right = new THREE.Vector3(-Math.cos(yaw), 0, Math.sin(yaw));
    const own = playerCarGroup.position.clone().setY(0);
    const axis = new THREE.Vector3(0, 0, own.z);
    const at = (lane, d) => axis.clone().addScaledVector(fwd, d).addScaledVector(right, lane === 'own' ? 1.8 : -1.8);
    // Stalled attract cars (a stand-off nobody resolves) quietly leave.
    state.actors.forEach(a => {
      if (!a.config?.id?.startsWith('attract_') || a.done) return;
      a.attractStill = a.speed < 0.1 && a.distance > 5 ? (a.attractStill || 0) + dt : 0;
      if (a.attractStill > 6) { a.done = true; a.mesh.visible = false; }
    });
    // Finished cars are disposed with their own group; the road segments are
    // never touched (they are trimmed by count, so extra entries would evict
    // the actual road).
    state.attractGroups = (state.attractGroups || []).filter(g => {
      const alive = state.actors.some(a => a.segment === g && !a.done);
      if (!alive) disposeSegment(g);
      return alive;
    });
    // One car at a time in the oncoming lane: the overtaking car uses it
    // too, so the two kinds never meet beside the player.
    const live = state.actors.filter(a => a.config?.id?.startsWith('attract_') && !a.done);
    const busy = live.some(a => {
      const d = a.mesh.position.clone().sub(own).dot(fwd);
      return a.attractBehind ? d < 32 : d > -8;
    });
    if (busy) return;
    const junction = state.intersections
      .map(i => (i.centerZ - own.z) * Math.sign(fwd.z || 1))
      .filter(d => d > 0).sort((a, b) => a - b)[0];
    const oncomingStart = Math.min(130, junction === undefined ? 130 : junction - 24);
    // Oncoming cars need room this side of the next junction (its actors wait
    // for the player there); otherwise every car comes from behind.
    const fromBehind = oncomingStart < 80 ? true : (state.attractTurn = !state.attractTurn);
    state.attractClock = 0; state.attractNext = 5 + Math.random() * 4;
    const group = new THREE.Group(); scene.add(group); state.attractGroups.push(group);
    const kinds = [['car', 'Авто', '#2BC280'], ['car', 'Авто', '#6E86A6'], ['truck', 'Грузовик', '#9AA0A6'], ['motorcycle', 'Мото', '#8B5CF6'], ['bus', 'Автобус', '#FFA53C']];
    const [type, name, color] = kinds[Math.floor(Math.random() * kinds.length)];
    const cfg = { id: 'attract_' + Date.now(), type, name, color };
    let actor;
    if (fromBehind) {
      // Swings into the oncoming lane well before the parked player and back after it.
      // Ends short of the next junction, where the scenario's actors wait.
      const end = Math.min(160, junction === undefined ? 160 : junction - 26);
      const pts = [at('own', -80), at('own', -30), at('opp', -14), at('opp', 10), at('own', 26), at('own', Math.max(40, end))];
      actor = addRoadActor(group, cfg, pts[0], yaw, pts, 9);
      actor.signalPlan = [{ from: 36, to: 62, side: 'left' }, { from: 84, to: 104, side: 'right' }];
    } else {
      const pts = [at('opp', oncomingStart), at('opp', 20), at('opp', -90)];
      actor = addRoadActor(group, cfg, pts[0], yaw + Math.PI, pts, 10);
    }
    actor.waitsForPlayer = false; actor.attractBehind = fromBehind;
  }

  // --- Garage reveal: a new car rolls out of a closed garage ---
  // Rendered in its own scene while active; the main scene is paused.
  let reveal = null;
  const REVEAL_TIMING = { door: 0.3, launch: 0.4, drift: 0.46, settle: 0.14 };
  function buildRevealScene(id, paint) {
    const sn = season();
    const rs = new THREE.Scene();
    // Garage sky shares the daylight world, independent of the UI theme.
    const skyTop = 0x9FD2F2, skyLow = 0xE6F4FC;
    const skyC = document.createElement('canvas'); skyC.width = 4; skyC.height = 256;
    const sg = skyC.getContext('2d'), grad = sg.createLinearGradient(0, 0, 0, 256);
    grad.addColorStop(0, '#' + skyTop.toString(16).padStart(6, '0'));
    grad.addColorStop(1, '#' + skyLow.toString(16).padStart(6, '0'));
    sg.fillStyle = grad; sg.fillRect(0, 0, 4, 256);
    rs.background = new THREE.CanvasTexture(skyC);
    rs.fog = new THREE.Fog(skyLow, 45, 120);
    rs.add(new THREE.AmbientLight(0xFFFFFF, sn.ambient));
    const sun = new THREE.DirectionalLight(sn.sun, sn.sunIntensity + 0.2); sun.position.set(-8, 14, -10); rs.add(sun);
    const mat = c => new THREE.MeshLambertMaterial({ color: c });
    // Procedural textures (canvas): paving, siding, shingles, concrete.
    const tex = (w, h, draw, rx = 1, ry = 1) => {
      const c = document.createElement('canvas'); c.width = w; c.height = h;
      draw(c.getContext('2d'), w, h);
      const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(rx, ry);
      t.anisotropy = Math.min(4, renderer.capabilities.getMaxAnisotropy());
      return t;
    };
    const hex = n => '#' + n.toString(16).padStart(6, '0');
    const shade = (n, k) => { const c = new THREE.Color(n); c.multiplyScalar(k); return '#' + c.getHexString(); };
    const texMat = (t, color = 0xFFFFFF) => new THREE.MeshLambertMaterial({ map: t, color });
    const paving = (base, rx, ry) => tex(256, 256, (g, w, h) => {
      g.fillStyle = hex(base); g.fillRect(0, 0, w, h);
      for (let row = 0; row < 8; row++) for (let col = 0; col < 4; col++) {
        const x = col * 64 + (row % 2) * 32, y = row * 32;
        g.fillStyle = shade(base, 0.9 + ((row * 7 + col * 3) % 5) * 0.03);
        g.fillRect(x + 2, y + 2, 60, 28); g.fillRect(x - 256 + 2, y + 2, 60, 28);
      }
    }, rx, ry);
    const planeY = (w, d, x, y, z, m) => { const p = new THREE.Mesh(new THREE.PlaneGeometry(w, d), m); p.rotation.x = -Math.PI / 2; p.position.set(x, y, z); p.receiveShadow = true; rs.add(p); return p; };
    const block = (w, h, d, x, y, z, m) => { const b = new THREE.Mesh(new THREE.BoxGeometry(w, h, d), m); b.position.set(x, y, z); b.castShadow = true; b.receiveShadow = true; rs.add(b); return b; };

    // Ground: lawn with a faint mottle.
    planeY(160, 160, 0, 0, 0, texMat(tex(128, 128, (g, w, h) => {
      g.fillStyle = hex(sn.ground); g.fillRect(0, 0, w, h);
      for (let i = 0; i < 380; i++) { g.fillStyle = shade(sn.ground, 0.92 + Math.random() * 0.14); g.fillRect(Math.random() * w, Math.random() * h, 2, 2); }
    }, 40, 40)));
    // Street: asphalt with edge lines and a broken centre line.
    planeY(120, 8.4, 0, 0.01, -31, texMat(tex(128, 128, (g, w, h) => {
      g.fillStyle = hex(BRAND.asphalt); g.fillRect(0, 0, w, h);
      for (let i = 0; i < 500; i++) { g.fillStyle = shade(BRAND.asphalt, 0.85 + Math.random() * 0.3); g.fillRect(Math.random() * w, Math.random() * h, 1, 1); }
    }, 30, 2)));
    const lineMat = mat(BRAND.asphaltMarking);
    for (const z of [-27.05, -34.95]) planeY(120, 0.14, 0, 0.014, z, lineMat);
    for (let x = -58; x <= 58; x += 5) planeY(2, 0.14, x, 0.014, -31, lineMat);
    // Pavement (raised, paved) with a stone kerb, cut for the driveway,
    // whose kerb is dropped flush.
    const paveMat = texMat(paving(sn.sidewalk, 2, 0.5));
    const kerbMat = mat(new THREE.Color(sn.sidewalk).multiplyScalar(0.78).getHex());
    for (const sx of [-1, 1]) {
      const w = 60 - 3.4, x = sx * (3.4 + w / 2);
      block(w, 0.12, 2.6, x, 0.06, -25.4, [mat(sn.sidewalk), mat(sn.sidewalk), paveMat, mat(sn.sidewalk), mat(sn.sidewalk), mat(sn.sidewalk)]);
      paveMat.map.repeat.set(w / 2.6, 1);
      block(w, 0.16, 0.22, x, 0.08, -26.8, kerbMat);
    }
    // Driveway: herringbone-ish paving between edging stones, running from
    // the road into the garage, flush with the dropped kerb.
    const driveMat = texMat(paving(new THREE.Color(sn.sidewalk).multiplyScalar(0.95).getHex(), 5, 20));
    planeY(6.4, 26.2, 0, 0.02, -13.7, driveMat); // ends at the garage floor, no overlap
    for (const sx of [-1, 1]) block(0.2, 0.08, 26.4, sx * 3.3, 0.04, -13.6, kerbMat);
    block(6.8, 0.06, 0.22, 0, 0.03, -26.8, kerbMat);

    // Neighbourhood behind the lot: trees, hedges and houses, clear of the
    // driveway and the camera's view line.
    [[-12, -6], [-15, 4], [13, -5], [16, 6], [-9, 12], [11, 13], [-22, -14], [22, -14]].forEach(([x, z]) => { const t = createTree(); t.position.set(x, 0, z); rs.add(t); });
    for (const sx of [-1, 1]) block(0.9, 1.0, 17, sx * 7.2, 0.5, -14.5, mat(0x4E7A48));
    [[-19, 10, 1], [19, 10, 1]].forEach(([x, z, style]) => { const h = createBuilding(9, 6, 8, style); h.position.set(x, 0, z); rs.add(h); });
    // Soft low-poly clouds: clusters of flattened white puffs in the sky.
    const cloudMat = new THREE.MeshLambertMaterial({ color: 0xFFFFFF, emissive: 0x3A4A55, fog: false });
    [[-26, 21, 70], [4, 25, 82], [30, 19, 66], [-8, 17, 58], [44, 24, 90]].forEach(([x, y, z], k) => {
      const cloud = new THREE.Group();
      [[0, 0, 0, 3.2], [2.8, 0.4, 0.4, 2.4], [-2.7, -0.2, 0.3, 2.2], [1.2, 1.4, -0.3, 2.3], [-1.1, 1.1, 0.2, 2.0]].forEach(([cx, cy, cz, r]) => {
        const puff = new THREE.Mesh(new THREE.IcosahedronGeometry(r, 1), cloudMat);
        puff.position.set(cx, cy, cz); cloud.add(puff);
      });
      cloud.scale.set(1.4 + (k % 2) * 0.4, 0.62, 0.8); cloud.position.set(x, y, z); rs.add(cloud);
    });
    // Behind the garage: two rows of trees, a hedge line and far hills.
    for (let i = 0; i < 16; i++) {
      const t = createTree(i % 3 === 0 ? 'pine' : undefined);
      t.position.set(-24 + i * 3.2 + (i % 2) * 0.8, 0, 11 + (i % 2) * 3.5); t.scale.setScalar(1.1 + (i % 3) * 0.15); rs.add(t);
    }
    for (let i = 0; i < 12; i++) {
      const t = createTree('pine'); t.position.set(-30 + i * 5.5, 0, 22 + (i % 3) * 2); t.scale.setScalar(1.5 + (i % 2) * 0.3); rs.add(t);
    }
    const hillMat = mat(new THREE.Color(sn.ground).multiplyScalar(0.82).getHex());
    [[-30, 60, 26], [8, 64, 30], [42, 58, 24]].forEach(([x, z, r]) => {
      const hill = new THREE.Mesh(new THREE.SphereGeometry(r, 18, 10), hillMat);
      hill.scale.set(1.6, 0.35, 1); hill.position.set(x, -2, z); rs.add(hill);
    });
    const lamp = createLampPost(); lamp.position.set(-6.5, 0, -24.4); rs.add(lamp);

    // The garage: siding walls with corner trims, a gable roof in shingles
    // with eaves and a gutter, a lintel with the door housing, lamps.
    const sidingT = tex(64, 256, (g, w, h) => {
      g.fillStyle = '#9EA6AD'; g.fillRect(0, 0, w, h);
      for (let y = 0; y < h; y += 16) { g.fillStyle = '#8A9299'; g.fillRect(0, y + 13, w, 3); g.fillStyle = '#AAB2B9'; g.fillRect(0, y, w, 2); }
    }, 3, 1.4);
    const wall = texMat(sidingT), inside = mat(0x6E757D), trimM = mat(0xE9ECEF), metalDark = mat(0x3A4148);
    const back = new THREE.Mesh(new THREE.BoxGeometry(9, 4.2, 0.3), inside); back.position.set(0, 2.1, 6.2); rs.add(back);
    [-1, 1].forEach(sx => {
      block(0.3, 4.2, 7, sx * 4.5, 2.1, 2.7, sx < 0 ? inside : wall);
      block(1.4, 4.2, 0.5, sx * 5.0, 2.1, -0.6, wall);
      block(0.16, 4.3, 0.16, sx * 5.72, 2.15, -0.86, trimM);          // corner trims
      block(0.16, 4.3, 0.16, sx * 4.66, 2.15, -0.86, trimM);          // door jambs
    });
    block(9.4, 0.7, 0.5, 0, 3.85, -0.6, wall);                         // lintel
    block(8.6, 0.34, 0.34, 0, 3.52, -0.2, metalDark);                       // door roll housing
    // Gable roof: two shingled slopes over the walls, ridge front to back.
    const shinglesT = tex(128, 128, (g, w, h) => {
      const base = sn.roof || 0x8C4A3C;
      g.fillStyle = hex(base); g.fillRect(0, 0, w, h);
      for (let y = 0; y < h; y += 16) for (let x = -((y / 16) % 2) * 8; x < w; x += 16) {
        g.fillStyle = shade(base, 0.86 + ((x + y) % 3) * 0.05); g.fillRect(x + 1, y + 1, 14, 13);
      }
    }, 4, 3);
    const roofM = texMat(shinglesT), rise = 1.7, half = 5.9, slopeLen = Math.hypot(half, rise), ang = Math.atan2(rise, half);
    for (const sx of [-1, 1]) {
      const slope = block(slopeLen + 0.2, 0.16, 8.2, sx * half / 2, 4.2 + rise / 2 + 0.08, 2.7, roofM);
      slope.rotation.z = -sx * ang;
      block(0.14, 0.14, 8.2, sx * (half + 0.05), 4.18, 2.7, metalDark);     // gutters
      block(0.1, 4.1, 0.1, sx * (half - 0.2), 2.05, -1.35, metalDark);      // downpipes
    }
    const gable = new THREE.Shape(); gable.moveTo(-5.7, 0); gable.lineTo(5.7, 0); gable.lineTo(0, rise); gable.closePath();
    const gableM = new THREE.Mesh(new THREE.ShapeGeometry(gable), wall);
    gableM.position.set(0, 4.2, -0.86); gableM.rotation.y = Math.PI; rs.add(gableM);
    // Wall lamps either side of the door, lit, and a house number.
    for (const sx of [-1, 1]) {
      block(0.24, 0.34, 0.2, sx * 5.1, 3.2, -0.95, metalDark);
      const bulb = block(0.16, 0.2, 0.06, sx * 5.1, 3.18, -1.06, new THREE.MeshBasicMaterial({ color: 0xFFE9B8 }));
      window.PDD_VEHICLES.addGlow(bulb, 0xFFD58A, 1.4);
      const lampLight = new THREE.PointLight(0xFFD58A, 0.35, 7); lampLight.position.set(sx * 5.1, 3.0, -1.6); rs.add(lampLight);
    }
    block(0.62, 0.36, 0.04, -5.0, 2.5, -0.88, mat(0x0574F8));
    const numC = document.createElement('canvas'); numC.width = 64; numC.height = 36;
    const ng = numC.getContext('2d'); ng.fillStyle = '#0574F8'; ng.fillRect(0, 0, 64, 36); ng.fillStyle = '#fff'; ng.font = 'bold 26px Arial'; ng.textAlign = 'center'; ng.fillText('12', 32, 28);
    const numFace = new THREE.Mesh(new THREE.PlaneGeometry(0.58, 0.32), new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(numC) }));
    numFace.position.set(-5.0, 2.5, -0.905); numFace.rotation.y = Math.PI; rs.add(numFace);
    // A side window on the near wall.
    block(0.06, 1.1, 1.8, -4.66, 2.4, 3.2, trimM);
    block(0.07, 0.9, 1.6, -4.67, 2.4, 3.2, mat(0x5E7890));
    // Concrete floor inside.
    planeY(8.4, 6.6, 0, 0.022, 2.7, texMat(tex(128, 128, (g, w, h) => {
      g.fillStyle = '#6B7178'; g.fillRect(0, 0, w, h);
      for (let i = 0; i < 300; i++) { g.fillStyle = shade(0x6B7178, 0.85 + Math.random() * 0.3); g.fillRect(Math.random() * w, Math.random() * h, 2, 2); }
      g.fillStyle = '#5D636A'; g.fillRect(0, h / 2 - 1, w, 2);
    }, 2, 2)));
    // Furnishings along the back and the far wall.
    const shelf = new THREE.Mesh(new THREE.BoxGeometry(3.4, 0.08, 0.5), mat(0xB0895C)); [1.3, 2.2, 3.1].forEach(y => { const m = shelf.clone(); m.position.set(-2.4, y, 5.8); rs.add(m); });
    const cans = [0xF08A24, 0x317ED4, 0xE8C547, 0xF2F3F5, 0x2FA3A0];
    for (let i = 0; i < 9; i++) { const can = new THREE.Mesh(new THREE.BoxGeometry(0.34, 0.4, 0.3), mat(cans[i % cans.length])); can.position.set(-3.8 + (i % 5) * 0.7, (i < 5 ? 1.3 : 2.2) + 0.24, 5.78); rs.add(can); }
    const board = new THREE.Mesh(new THREE.BoxGeometry(2.4, 1.6, 0.06), mat(0x9E7A4E)); board.position.set(2.4, 2.4, 6.0); rs.add(board);
    [[-0.8, 0.4], [-0.3, 0.5], [0.3, 0.4], [0.8, 0.5], [0, -0.3]].forEach(([x, y]) => { const tool = new THREE.Mesh(new THREE.BoxGeometry(0.12, 0.7, 0.05), mat(0x3B4148)); tool.position.set(2.4 + x, 2.4 + y, 5.94); rs.add(tool); });
    for (let i = 0; i < 4; i++) { const tyre = new THREE.Mesh(new THREE.TorusGeometry(0.42, 0.16, 8, 14), mat(0x24282C)); tyre.rotation.x = Math.PI / 2; tyre.position.set(3.6, 0.18 + i * 0.34, 4.6); rs.add(tyre); }
    const bench = new THREE.Mesh(new THREE.BoxGeometry(0.7, 0.9, 2.2), mat(0x5B6169)); bench.position.set(-3.9, 0.45, 2.4); rs.add(bench);
    const benchTop = new THREE.Mesh(new THREE.BoxGeometry(0.8, 0.08, 2.3), mat(0xB0895C)); benchTop.position.set(-3.9, 0.94, 2.4); rs.add(benchTop);
    const strip = new THREE.Mesh(new THREE.BoxGeometry(2.6, 0.08, 0.2), mat(0xFFF4D6)); strip.position.set(0, 4.0, 2.6); rs.add(strip);
    const glow = new THREE.PointLight(0xFFE2B0, 0.7, 14); glow.position.set(0, 3.7, 2.6); rs.add(glow);
    // Door: a slatted panel that rolls up under the lintel.
    const door = new THREE.Group();
    for (let i = 0; i < 8; i++) {
      const slat = new THREE.Mesh(new THREE.BoxGeometry(8.4, 0.5, 0.12), mat(i % 2 ? 0xC9CFD4 : 0xBAC1C7));
      slat.position.y = 0.28 + i * 0.52; door.add(slat);
    }
    door.position.set(0, 0, -0.7); rs.add(door);
    const car = window.PDD_VEHICLES.create(id, paint);
    car.position.set(1.1, 0, 2.6); car.rotation.y = Math.PI; // room for the final parking arc
    rs.add(car);
    // Celebration: headlights, light pouring out of the opening door, a
    // glowing pad where the car stops, sparkles round it and confetti.
    const additive = (color, opacity) => new THREE.MeshBasicMaterial({ color, transparent: true, opacity, blending: THREE.AdditiveBlending, depthWrite: false, side: THREE.DoubleSide });
    const rays = new THREE.Group();
    for (let i = 0; i < 5; i++) {
      const shape = new THREE.Shape(); const w = 0.9 + i * 0.35;
      shape.moveTo(-w, 0); shape.lineTo(w, 0); shape.lineTo(w * 2.2, -9); shape.lineTo(-w * 2.2, -9); shape.closePath();
      const ray = new THREE.Mesh(new THREE.ShapeGeometry(shape), additive(0xFFE6A8, 0));
      ray.rotation.x = -Math.PI / 2; ray.position.set((i - 2) * 1.5, 0.03 + i * 0.002, -0.7);
      rays.add(ray);
    }
    rays.visible = false; // no light shafts on the floor (they flickered)
    rs.add(rays);
    const pad = new THREE.Mesh(new THREE.RingGeometry(2.6, 3.0, 64), additive(0x3F8CFF, 0));
    pad.rotation.x = -Math.PI / 2; pad.position.set(0, 0.045, -6.6); rs.add(pad);
    const padFill = new THREE.Mesh(new THREE.CircleGeometry(2.4, 48), additive(0x2F7BF0, 0));
    padFill.rotation.x = -Math.PI / 2; padFill.position.set(0, 0.035, -6.6); rs.add(padFill);
    const sparkles = [];
    for (let i = 0; i < 18; i++) {
      const holder = new THREE.Object3D();
      window.PDD_VEHICLES.addGlow(holder, [0xFFE27A, 0xFFFFFF, 0x9FD0FF][i % 3], 0.28 + Math.random() * 0.22);
      holder.visible = false; rs.add(holder);
      sparkles.push({ holder, angle: i / 18 * Math.PI * 2, radius: 2.6 + Math.random() * 1.4, height: 0.4 + Math.random() * 2.2, speed: 0.4 + Math.random() * 0.6, phase: Math.random() * 6 });
    }
    // Two small launchers at the threshold: flat paper and long ribbons,
    // rendered in one draw call instead of round points.
    const confetti = new THREE.InstancedMesh(new THREE.PlaneGeometry(1, 1),
      new THREE.MeshBasicMaterial({ side: THREE.DoubleSide, transparent: true, depthWrite: false, fog: false }), 200);
    confetti.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    const palette = [0xFF366F, 0xFFD629, 0x18DFFF, 0xA35BFF, 0xFF8329, 0x46ED97, 0xFFFFFF];
    const cPieces = Array.from({ length: confetti.count }, (_, i) => {
      confetti.setColorAt(i, new THREE.Color(palette[i % palette.length]));
      return { position: new THREE.Vector3(), velocity: new THREE.Vector3(),
        rotation: new THREE.Vector3(), tumble: new THREE.Vector3(),
        width: 0.09 + Math.random() * 0.07, height: i % 7 === 0 ? 0.65 : 0.17 + Math.random() * 0.12 };
    });
    confetti.visible = false; confetti.frustumCulled = false; rs.add(confetti);
    // A bounded pool of soft, translucent tyre puffs; no lights or new
    // geometry are allocated while animating.
    const smokeMap = tex(64, 64, g => {
      g.clearRect(0, 0, 64, 64);
      const gradient = g.createRadialGradient(32, 32, 3, 32, 32, 30);
      gradient.addColorStop(0, 'rgba(255,255,255,0.8)');
      gradient.addColorStop(0.45, 'rgba(255,255,255,0.45)');
      gradient.addColorStop(1, 'rgba(255,255,255,0)');
      g.fillStyle = gradient; g.fillRect(0, 0, 64, 64);
    });
    smokeMap.wrapS = smokeMap.wrapT = THREE.ClampToEdgeWrapping;
    const smoke = Array.from({ length: 48 }, () => {
      const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: smokeMap, color: 0xE6E4DF,
        transparent: true, opacity: 0, depthWrite: false }));
      sprite.visible = false; rs.add(sprite);
      return { sprite, age: 1, life: 0.7, velocity: new THREE.Vector3() };
    });
    const skidGeometry = new THREE.PlaneGeometry(1, 1); skidGeometry.rotateX(-Math.PI / 2);
    const skids = new THREE.InstancedMesh(skidGeometry,
      new THREE.MeshBasicMaterial({ color: 0x282629, transparent: true, opacity: 0.2, depthWrite: false }), 128);
    skids.instanceMatrix.setUsage(THREE.DynamicDrawUsage); skids.count = 0; skids.frustumCulled = false; rs.add(skids);
    // Three-quarter view from the driveway: the whole garage front and the
    // spot where the car stops are in frame on a portrait screen.
    // Aimed at the spot where the car stops (x 0, z -6.6): the car sits in
    // the middle of the screen with the open garage behind it.
    const cam = new THREE.PerspectiveCamera(46, 1, 0.1, 160);
    cam.position.set(-4.2, 5.2, -20.5); cam.lookAt(0, 0.1, -6.6);
    return { scene: rs, camera: cam, door, car, phase: 'closed', t: 0, yaw: 0, spin: 0,
      noseLength: (new THREE.Box3().setFromObject(car)).getSize(new THREE.Vector3()).z / 2,
      fx: { rays, pad, padFill, sparkles, confetti, cPieces, skids, skidPrev: [], skidAge: 0, dummy: new THREE.Object3D(), smoke, smokeClock: 0, smokeIndex: 0, time: 0, burst: false, burstAge: 0 } };
  }
  function burstRevealConfetti(r) {
    const fx = r.fx; fx.burst = true; fx.burstAge = 0; fx.confetti.visible = true;
    gameAudio?.celebrate('fanfare');
    fx.cPieces.forEach((p, i) => {
      const side = i % 2 ? 1 : -1;
      p.position.set(side * 3.3, 0.8, -1.5);
      p.velocity.set(-side * (1 + Math.random() * 4), 5 + Math.random() * 4, -1 - Math.random() * 5);
      p.rotation.set(Math.random() * 6, Math.random() * 6, Math.random() * 6);
      p.tumble.set(4 + Math.random() * 8, (Math.random() - 0.5) * 10, (Math.random() - 0.5) * 12);
    });
  }
  function emitRevealSmoke(r, dt, drifting) {
    const fx = r.fx; fx.smokeClock += dt; r.car.updateMatrixWorld(true);
    while (fx.smokeClock >= 0.03) {
      fx.smokeClock -= 0.03;
      r.car.userData.wheels.filter(wh => wh.parent.position.z < 0).forEach(wh => {
        const puff = fx.smoke[fx.smokeIndex++ % fx.smoke.length];
        wh.getWorldPosition(puff.sprite.position); puff.sprite.position.y = 0.14;
        puff.age = 0; puff.life = drifting ? 0.7 : 0.4; puff.strength = drifting ? 1 : 0.65;
        const outward = Math.sign(wh.parent.position.x) * (drifting ? 1.8 : 0.6);
        puff.velocity.set(Math.cos(r.car.rotation.y) * outward + (Math.random() - 0.5) * 0.6,
          1 + Math.random() * 0.5, -Math.sin(r.car.rotation.y) * outward + 0.4);
        puff.sprite.material.rotation = Math.random() * Math.PI; puff.sprite.visible = true;
      });
    }
  }
  function updateRevealSkids(r) {
    const fx = r.fx; r.car.updateMatrixWorld(true);
    r.car.userData.wheels.filter(wh => wh.parent.position.z < 0).forEach((wh, i) => {
      const point = wh.getWorldPosition(new THREE.Vector3()); point.y = 0.028;
      const previous = fx.skidPrev[i], length = previous ? previous.distanceTo(point) : 0;
      if (length > 0.005 && fx.skids.count < 128) {
        fx.dummy.position.copy(previous).add(point).multiplyScalar(0.5);
        fx.dummy.rotation.set(0, Math.atan2(previous.x - point.x, previous.z - point.z), 0);
        fx.dummy.scale.set(0.13, 1, length + 0.015); fx.dummy.updateMatrix();
        fx.skids.setMatrixAt(fx.skids.count++, fx.dummy.matrix);
        fx.skids.instanceMatrix.needsUpdate = true;
      }
      fx.skidPrev[i] = point;
    });
  }
  function updateReveal(dt) {
    const r = reveal; if (!r) return;
    const w = container.clientWidth || window.innerWidth, h = container.clientHeight || window.innerHeight;
    r.camera.aspect = w / h; r.camera.updateProjectionMatrix();
    const fx = r.fx; fx.time += dt;
    if (r.phase === 'opening' && r.t === 0) gameAudio?.celebrate('door');
    if (r.phase === 'opening') {
      r.t += dt; const u = Math.min(1, r.t / REVEAL_TIMING.door);
      fx.rays.children.forEach((ray, i) => { ray.material.opacity = 0.16 * u * (0.8 + 0.2 * Math.sin(fx.time * 3 + i)); });
      r.door.position.y = 4.3 * (1 - Math.pow(1 - u, 3));
      r.door.children.forEach(slat => { slat.visible = slat.position.y + r.door.position.y < 3.75; });
      if (u >= 1) { r.phase = 'driving'; r.t = 0; }
    } else if (r.phase === 'driving') {
      const before = r.car.position.z;
      r.t += dt; const u = Math.min(1, r.t / REVEAL_TIMING.launch);
      // Strong launch; exit speed matches the beginning of the slide (~11 m/s).
      const e = u * u * (2.375 - 1.375 * u);
      r.car.position.z = 2.6 - 7.1 * e;
      r.car.userData.frontAxles?.forEach(axle => { axle.rotation.y = 0.32 * Math.max(0, (u - 0.8) / 0.2); });
      r.car.rotation.x = -0.025 * Math.sin(u * Math.PI);
      const distance = before - r.car.position.z;
      r.car.userData.wheels.forEach(wh => wh.rotateX(-distance / Math.max(0.2, wh.parent.position.y)));
      if (!fx.burst && r.car.position.z - r.noseLength <= -0.9) burstRevealConfetti(r);
      if (distance > 0) emitRevealSmoke(r, dt, false);
      if (u >= 1) {
        r.phase = 'drifting'; r.t = 0; r.car.rotation.x = 0;
        updateRevealSkids(r); // capture rear tyre contacts before the slide
      }
    } else if (r.phase === 'drifting') {
      const before = r.car.position.clone();
      r.t += dt; const u = Math.min(1, r.t / REVEAL_TIMING.drift), v = 1 - u;
      // Forward momentum continues while the rear swings out. Translation
      // and heading are deliberately separate: a slide, not a parking arc.
      r.car.position.set(1.1 * (1 - u * u * (3 - 2 * u)), 0,
        -4.5 * v * v * v - 3 * 6.2 * v * v * u - 3 * 6.6 * v * u * u - 6.6 * u * u * u);
      const turn = Math.min(1, u / 0.78);
      r.car.rotation.y = Math.PI + (Math.PI / 2 + 0.08) * turn * turn * (3 - 2 * turn);
      r.car.rotation.z = -0.015 * Math.sin(Math.PI * u);
      // Countersteer into the skid, then straighten as grip returns.
      r.car.userData.frontAxles?.forEach(axle => { axle.rotation.y = 0.32 * Math.exp(-18 * u) - 0.52 * Math.sin(Math.PI * u); });
      const distance = before.distanceTo(r.car.position);
      r.car.userData.wheels.forEach(wh => wh.rotateX(-distance / Math.max(0.2, wh.parent.position.y)));
      if (u < 0.92) emitRevealSmoke(r, dt, true);
      updateRevealSkids(r);
      if (u >= 1) { r.phase = 'settling'; r.t = 0; }
    } else if (r.phase === 'settling') {
      r.t += dt; const u = Math.min(1, r.t / REVEAL_TIMING.settle);
      r.car.rotation.y = Math.PI * 1.5 + 0.08 * (1 - u) * (1 - u);
      r.car.rotation.z = 0.012 * Math.sin(u * Math.PI * 2) * (1 - u);
      r.car.userData.frontAxles?.forEach(axle => { axle.rotation.y = 0; });
      if (u >= 1) {
        r.car.position.set(0, 0, -6.6); r.car.rotation.set(0, Math.PI * 1.5, 0);
        r.phase = 'shown'; r.t = 0; r.yaw = r.car.rotation.y; sendToFlutter({ event: 'reveal_shown' });
        fx.sparkles.forEach(sp => { sp.holder.visible = true; });
      }
    } else if (r.phase === 'shown') {
      // Free spin by finger; drifts slowly when idle.
      r.t += dt; r.yaw += (r.spin + (r.t > 1 ? 0.1 : 0)) * dt; r.spin *= Math.pow(0.05, dt);
      r.car.rotation.y = r.yaw;
      if (Math.floor(fx.time * 1.4) !== Math.floor((fx.time - dt) * 1.4) && Math.random() < 0.5) gameAudio?.celebrate('sparkle');
    }
    if (r.phase === 'lobby') {
      // The garage start screen: the car waits outside, turning slowly.
      r.yaw += (r.spin + 0.22) * dt; r.spin *= Math.pow(0.05, dt);
      r.car.rotation.y = r.yaw;
      if (r.swap) {
        const sw = r.swap; sw.t += dt;
        const u = Math.min(1, sw.t / 0.45), e = u < 0.5 ? 2 * u * u : 1 - Math.pow(-2 * u + 2, 2) / 2;
        sw.from.position.x = 9 * sw.dir * e;
        sw.to.position.x = -9 * sw.dir * (1 - e);
        sw.from.rotation.y = r.yaw;
        [sw.from, sw.to].forEach(c => c.userData.wheels?.forEach(w => w.rotateX(dt * 9 * (1 - Math.abs(e - 0.5) * 2 + 0.1))));
        if (u >= 1) {
          r.scene.remove(sw.from);
          sw.from.traverse(o => { if (o.geometry) o.geometry.dispose(); });
          r.swap = null;
        }
      }
    }
    if (['driving', 'drifting', 'settling', 'shown', 'lobby'].includes(r.phase)) {
      // Light keeps pouring out; the pad under the car pulses.
      fx.rays.children.forEach((ray, i) => { ray.material.opacity = 0.14 + 0.04 * Math.sin(fx.time * 2.5 + i); });
      const pulse = 0.5 + 0.5 * Math.sin(fx.time * 3);
      const k = r.phase === 'shown' || r.phase === 'lobby' ? 1 : r.phase === 'settling' ? 1 : r.phase === 'drifting' ? Math.min(1, r.t / REVEAL_TIMING.drift) : 0;
      fx.pad.material.opacity = k * (0.16 + 0.12 * pulse); fx.padFill.material.opacity = k * (0.05 + 0.04 * pulse);
      fx.pad.scale.setScalar(1 + 0.05 * pulse);
    }
    fx.sparkles.forEach(sp => {
      if (!sp.holder.visible) return;
      const a = sp.angle + fx.time * sp.speed;
      sp.holder.position.set(r.car.position.x + Math.cos(a) * sp.radius, sp.height + 0.3 * Math.sin(fx.time * 2 + sp.phase), r.car.position.z + Math.sin(a) * sp.radius);
      sp.holder.scale.setScalar(0.4 + 0.6 * Math.abs(Math.sin(fx.time * 4 + sp.phase)));
    });
    fx.smoke.forEach(puff => {
      if (!puff.sprite.visible) return;
      puff.age += dt; const u = Math.min(1, puff.age / puff.life);
      puff.sprite.position.addScaledVector(puff.velocity, dt);
      puff.sprite.scale.setScalar(0.45 + Math.sqrt(u) * 2.3);
      puff.sprite.material.opacity = puff.strength * 0.8 * Math.min(1, u / 0.12) * Math.pow(1 - u, 1.5);
      if (u >= 1) puff.sprite.visible = false;
    });
    if (r.phase === 'shown' && fx.skids.count) {
      fx.skidAge += dt; fx.skids.material.opacity = 0.2 * Math.max(0, 1 - fx.skidAge / 2.5);
    }
    if (fx.burst && fx.confetti.visible) {
      fx.burstAge += dt;
      const fade = Math.max(0, 1 - Math.max(0, fx.burstAge - 2) / 1.1);
      fx.cPieces.forEach((p, i) => {
        p.velocity.y -= 5.5 * dt;
        p.velocity.multiplyScalar(Math.pow(0.7, dt));
        p.position.addScaledVector(p.velocity, dt);
        p.position.x += Math.sin(fx.burstAge * 9 + i) * dt * 0.35;
        p.rotation.addScaledVector(p.tumble, dt);
        if (p.position.y < 0.06) { p.position.y = 0.06; p.velocity.set(0, 0, 0); p.rotation.x = -Math.PI / 2; }
        fx.dummy.position.copy(p.position); fx.dummy.rotation.set(p.rotation.x, p.rotation.y, p.rotation.z);
        fx.dummy.scale.set(p.width * fade, p.height * fade, 1); fx.dummy.updateMatrix();
        fx.confetti.setMatrixAt(i, fx.dummy.matrix);
      });
      fx.confetti.instanceMatrix.needsUpdate = true;
      if (fade === 0) fx.confetti.visible = false;
    }
    renderer.render(r.scene, r.camera);
  }

  // Offscreen thumbnail of any model/paint, for the garage list.
  let thumbRenderer = null;
  function renderThumbnail(id, paint) {
    if (!thumbRenderer) { thumbRenderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, preserveDrawingBuffer: true }); thumbRenderer.setSize(280, 180); thumbRenderer.setPixelRatio(1); }
    const ts = new THREE.Scene();
    ts.add(new THREE.AmbientLight(0xFFFFFF, 0.7));
    const key = new THREE.DirectionalLight(0xFFF4E0, 0.8); key.position.set(4, 8, 6); ts.add(key);
    const car = window.PDD_VEHICLES.create(id, paint); car.rotation.y = 0.5; ts.add(car);
    // Front three-quarter view, the car centred in the frame.
    const cam = new THREE.OrthographicCamera(-2.7, 2.7, 1.75, -1.75, 0.1, 50);
    cam.position.set(7, 3.4, 8); cam.lookAt(0, 0.65, 0);
    thumbRenderer.setClearColor(0x000000, 0);
    thumbRenderer.render(ts, cam);
    const url = thumbRenderer.domElement.toDataURL('image/png');
    car.traverse(o => { if (o.geometry) o.geometry.dispose(); if (o.material) o.material.dispose(); });
    return url;
  }

  function clearOncoming() {
    state.oncomingSeconds = 0;
    state.oncomingPenalized = false;
    if (state.oncoming) {
      state.oncoming = false;
      state.oncomingAgainst = false;
      sendToFlutter({ event: 'lane_changed', lane: 'right', oncoming: false });
    }
  }

  // oncoming: the left lane of a two-way road (3 s grace for a manoeuvre).
  // against: driving against the flow of a one-way road — any lane, no grace
  // beyond a moment; the notice says so instead of "keep right".
  function updateLaneViolation(dt, oncoming = state.currentLaneOffset > -0.85, against = false) {
    oncoming = oncoming || against;
    if (oncoming !== state.oncoming || (oncoming && against !== !!state.oncomingAgainst)) {
      state.oncoming = oncoming;
      state.oncomingAgainst = oncoming && against;
      state.oncomingSeconds = 0;
      state.oncomingPenalized = false;
      sendToFlutter({ event: 'lane_changed', lane: against ? 'against' : oncoming ? 'left' : 'right', oncoming });
      if (oncoming) state.oncomingEpisode = ++state.violationEpisode;
      return;
    }
    if (oncoming && !state.oncomingPenalized) {
      state.oncomingSeconds += dt;
      if (state.oncomingSeconds + 1e-9 < (against ? 1 : 3)) return;
      state.oncomingPenalized = true;
      if (against) highlightMistake({ type: 'one_way' });
      sendToFlutter({ event: 'violation', type: against ? 'one_way' : 'oncoming', episode: state.oncomingEpisode });
    }
  }

  // The one-way mode of the road under the player: null on two-way roads,
  // else whether the player's heading goes with or against the flow.
  function oneWayStatus() {
    const oneWayQuestion = state.roadEvent;
    if (oneWayQuestion?.scene?.oneWayRoad && playerCarGroup.position.z >= oneWayQuestion.stopZ + 10 && playerCarGroup.position.z <= oneWayQuestion.endZ) return Math.cos(playerCarGroup.rotation.y) < -0.3 ? 'against' : 'with';
    const mode = currentCorridor?.userData.oneWay;
    if (!mode) return null;
    const ends = corridorWorldEnds();
    const z = playerCarGroup.position.z;
    // The road starts at the junction it leaves (its cross arm is part of
    // the same street), so the stretch begins ~15 m before the seam.
    if (!ends.length || z < Math.min(...ends.map(p => p.z)) - 16 || z > Math.max(...ends.map(p => p.z)) + 2) return null;
    // Heading relative to the road's own +Z (its flow when built 'with'):
    // stays right after the world is turned round behind a U-turn.
    const axis = new THREE.Vector3(0, 0, 1).transformDirection(currentCorridor.matrixWorld);
    const c = axis.x * Math.sin(playerCarGroup.rotation.y) + axis.z * Math.cos(playerCarGroup.rotation.y);
    if (Math.abs(c) < 0.3) return state.oneWayAgainst ? 'against' : 'with'; // sideways: keep the last verdict
    state.oneWayAgainst = (mode === 'against') !== (c < 0);
    return state.oneWayAgainst ? 'against' : 'with';
  }

  let lastTime = null, telemetryElapsed = 0;
  function animate(time) {
    requestAnimationFrame(animate);
    const elapsed = lastTime === null ? 0 : Math.max(0, (time - lastTime) / 1000);
    const dt = Math.min(elapsed, 0.05);
    lastTime = time;
    // The ceremony follows wall time even below 20 FPS; road physics retains
    // its smaller integration step. A background/resume gap stays bounded.
    if (reveal) { updateReveal(Math.min(elapsed, 0.1)); return; }
    if (state.paused) return;
    if (!state.paused) {
      updateAttract(dt);
      updateActors(dt);
      if (state.resolution) updateResolution(dt);
      else updatePlayerMovement(dt);
      updateRoadEvent(dt);
      updateWeather(dt);
      updateBlinkers(dt);
      updateMistakeHighlight(dt);
      gameAudio?.update(dt, time / 1000);
      state.roadSegments.forEach(seg => seg.traverse(obj => {
        if (obj.userData.beacons) obj.userData.beacons.forEach((lamp, i) => {
          lamp.visible = Math.floor(time / 180 + i) % 2 === 0;
        });
      }));
      terrainMesh.position.z = playerCarGroup.position.z + 500;
      updateCamera(dt);
      checkAndSpawnNext();
      telemetryElapsed += dt;
      if (telemetryElapsed >= 0.2) {
        telemetryElapsed = 0;
        sendToFlutter({ event: 'telemetry', speedKmH: Math.round(Math.abs(state.speed) * 3.6),
          distanceM: Math.round(state.distanceTraveled), limitKmH: effectiveLimitKmH() });
      }
    }
    renderer.render(scene, camera);
  }

  function updateBlinkers(dt) {
    playerCarGroup.userData.frontAxles?.forEach(axle => { axle.rotation.y = (state.steering || 0) * 0.4; });
    playerWheels.forEach(w => w.rotateX(state.speed * dt / 0.35));
    playerCarGroup.brakeLights.forEach(light => {
      light.material.color.setHex(state.isBraking || state.speed === 0 || !state.isAccelerating ? 0xF04438 : 0x7F1D1D);
    });
    if (state.hazard > 0) {
      // The player's own hazard lights after a crash, for a few seconds.
      state.hazard = Math.max(0, state.hazard - dt);
      state.hazardClock = (state.hazardClock || 0) + dt;
      const on = Math.floor(state.hazardClock * 3) % 2 === 0;
      playerCarGroup.blinkerL.visible = playerCarGroup.blinkerR.visible = on;
      if (on && !gameAudio?.blinkerOn) gameAudio?.click();
      if (gameAudio) gameAudio.blinkerOn = on;
      return;
    }
    state.steerHold = state.steering ? (state.steerHold || 0) + dt : 0;
    if (state.steering && state.steerHold >= 0.3) {
      const side = state.steering > 0 ? 'left' : 'right';
      if (state.blinker?.side !== side) state.blinker = { side, remaining: 2.2, elapsed: 0 };
    }
    const b = state.blinker;
    if (b) {
      b.remaining = state.steering && b.side === (state.steering > 0 ? 'left' : 'right') ? 2.2 : b.remaining - dt;
      b.elapsed += dt;
      if (b.remaining <= 0) state.blinker = null;
    }
    playerCarGroup.blinkerL.visible = !!(state.blinker && b.side === 'left' && Math.floor(b.elapsed * 3) % 2 === 0);
    playerCarGroup.blinkerR.visible = !!(state.blinker && b.side === 'right' && Math.floor(b.elapsed * 3) % 2 === 0);
    const blinkerOn = playerCarGroup.blinkerL.visible || playerCarGroup.blinkerR.visible;
    if (blinkerOn && !gameAudio?.blinkerOn) gameAudio?.click();
    if (gameAudio) gameAudio.blinkerOn = blinkerOn;
  }

  // Gentle driving aid for newcomers: with the steering released on the open
  // road the car straightens along the road and drifts towards the middle of
  // the nearest lane. Any steering input takes over completely.
  // Lane centres lie at ±1.8, ±5.4, … from the road axis; a lane counts
  // when the whole car width fits on the asphalt a little ahead.
  function laneFits(x) {
    const frame=curvedRoadFrame();
    if(frame) {
      const sign=Math.cos(playerCarGroup.rotation.y-frame.yaw)<0?-1:1;
      const offset=frame.offsetOf(x),z=frame.local.z+sign*3;
      return roadSupports(frame.pointAt(offset-1.1,z))&&roadSupports(frame.pointAt(offset+1.1,z));
    }
    const z = playerCarGroup.position.z + Math.sign(Math.cos(playerCarGroup.rotation.y) || 1) * 3;
    return roadSupports(new THREE.Vector3(x - 1.1, 0, z)) && roadSupports(new THREE.Vector3(x + 1.1, 0, z));
  }

  function nearestLaneX(x) {
    const frame=curvedRoadFrame();
    if(frame) {
      const sign=Math.cos(playerCarGroup.rotation.y-frame.yaw)<0?-1:1;
      const offset=frame.offsetOf(x),oncoming=offset*sign>.85;
      return frame.pointAt(oncoming?1.8*sign:-1.8*sign,frame.local.z).x;
    }
    // On a two-way road the oncoming lanes count only for a car already in
    // one (overtaking): a car left on the centre line (after a bump, a turn
    // gone wrong) is taken back to its own side, never across it.
    const heading = Math.cos(playerCarGroup.rotation.y) < 0 ? -1 : 1;
    const twoWay = !oneWayStatus();
    let best = null;
    for (let k = 0; k < 4; k++) for (const c of [1.8 + 3.6 * k, -1.8 - 3.6 * k]) {
      if (!laneFits(c)) continue;
      const oncoming = twoWay && c * heading > 0;
      if (oncoming && Math.abs(c - x) > 1) continue;
      if (best == null || Math.abs(c - x) < Math.abs(best - x)) best = c;
    }
    return best ?? -1.8 * heading;
  }

  function changeLane(direction) {
    if (!playerCarGroup || state.paused || state.driveRecovery) return;
    if (state.resolution) {
      if (state.resolution.phase === 'manual' && !state.resolution.recovery) chooseJunctionExit(direction);
      return;
    }
    if (state.isAtSituation) return;
    const car = playerCarGroup, back = Math.cos(car.rotation.y) < 0, sign = back ? -1 : 1;
    // Never start a lane change the question stop would cut in half: the car
    // would stand diagonally across the lanes.
    const stops = [...state.intersections.map(it => it.stopZ), state.roadEvent?.phase === 'approach' ? state.roadEvent.stopZ : null];
    // Back to one's own side is always allowed: stopping for a question out
    // in the oncoming lane is worse than a stop mid-change.
    const frame=curvedRoadFrame();
    const laneSide = frame ? frame.offset * Math.sign(Math.cos(car.rotation.y-frame.yaw) || 1) : car.position.x;
    const homeward = !back && direction === 'right' && laneSide > 0.85;
    if (!back && !homeward && stops.some(z => z != null && z - car.position.z > -2 && z - car.position.z < 28)) {
      if (state.simpleSteering) refuseInput();
      return;
    }
    // Forward is +Z, so the driver's left is +X; heading back mirrors it.
    // Wide streets have more lanes: step one lane over if there is road.
    const from = frame && state.curveLaneTarget!=null && state.laneChangeX!=null
      ? frame.pointAt(state.curveLaneTarget,frame.local.z).x : state.laneChangeX ?? nearestLaneX(car.position.x);
    const to = from + (direction === 'left' ? 3.6 : -3.6) * sign;
    if (!laneFits(to)) { if (state.simpleSteering) refuseInput(); return; }
    state.laneChangeX = to;
    planLaneCurve(to);
    triggerBlinker(direction);
  }

  // An S-curve that ends exactly on the lane centre, parallel to the road.
  function planLaneCurve(to) {
    const frame=curvedRoadFrame();
    if(frame) {
      const sign=Math.cos(playerCarGroup.rotation.y-frame.yaw)<0?-1:1;
      const length=Math.max(12,Math.abs(state.speed)*1.5),target=frame.offsetOf(to),points=[];
      state.curveLaneTarget=target;
      const count=Math.ceil(length/.5);
      for(let i=0;i<=count;i++) {
        const t=i/count,d=length*t,e=t*t*t*(10+t*(-15+6*t));
        points.push(frame.pointAt(frame.offset+(target-frame.offset)*e,frame.local.z+sign*d));
      }
      state.autoPath=planPath(curve(points));return;
    }
    const car = playerCarGroup, sign = Math.cos(car.rotation.y) < 0 ? -1 : 1;
    const start = car.position.clone();
    const length = Math.max(9, Math.abs(state.speed) * 1.05);
    const end = new THREE.Vector3(to, 0, start.z + sign * length);
    state.autoPath = planPath(new THREE.CubicBezierCurve3(start,
      new THREE.Vector3(start.x, 0, start.z + sign * length * 0.45),
      new THREE.Vector3(to, 0, end.z - sign * length * 0.45), end));
  }

  function planPath(path) {
    return { path, length: path.getLength(), s: 0 };
  }

  // At a junction an arrow picks the exit (only roads that exist); the car
  // then drives it by itself. Pressing the same arrow again goes back to
  // straight on. The choice is open until the car reaches the turn.
  // Left pressed again on a chosen left turn means a U-turn (where one
  // fits); once more — straight on again.
  // Each exit stays open until the car reaches the point where that very
  // manoeuvre begins: a car waiting at the median stop line can still turn
  // left, the turn itself starts beyond it.
  function exitGate(r, c) {
    const z = r.intersection.centerZ + (r.spec.exitOffsets?.[c] || 0), R = r.intersection.rightLane || 1.8;
    if (r.intersection.situation.geometry === 'roundabout') return z - 17;
    return c === 'right' ? z - R - 3 : c === 'left' ? z - 2.5 : c === 'uturn' ? z - 3.5 : Infinity;
  }

  // A U-turn needs the whole crossing: not on a ring, at a T, across a
  // median or where a motorway joins (16.1).
  function uturnFits(r) {
    // Reviewed 27.9 crosses both carriageways before returning; the generic
    // short U-turn would instead cross the median.
    if (r.intersection.previews?.uturn && r.spec.reviewed && r.spec.paths?.uturn &&
        (r.spec.allowedManeuvers || [r.spec.maneuver]).includes('uturn')) return true;
    return !!r.intersection.previews?.uturn && !['roundabout', 't_no_straight', 'divided_road', 'motorway_merge', 'motorway_parallel']
      .includes(r.intersection.situation.geometry);
  }

  // The U-turn button can still be used here (Flutter shows it only then).
  function uturnOffered(r) {
    if (!r || !state.simpleSteering || r.phase !== 'manual' || r.recovery || !uturnFits(r)) return false;
    const pz = playerCarGroup.position.z;
    if (r.simpleChoice && r.simpleChoice !== 'straight' && r.simpleChoice !== 'uturn' && pz > exitGate(r, r.simpleChoice)) return false;
    // Only while the car still heads into the junction: a U-turn under way
    // comes back below its gate, and the button used to show up again.
    if (Math.cos(playerCarGroup.rotation.y) < 0.9) return false;
    return pz <= exitGate(r, 'uturn');
  }

  // Arrows: «←» left, «→» right, the same arrow again — straight on. The
  // U-turn has its own button ('uturn', pressed again — straight on).
  function chooseJunctionExit(direction) {
    const r = state.resolution, previews = r.intersection.previews || {};
    const pz = playerCarGroup.position.z, gateFor = c => exitGate(r, c);
    // A turn already under way is committed: past its gate, or already
    // turned well away from the approach (a U-turn comes back below it).
    if (r.simpleChoice && r.simpleChoice !== 'straight' &&
        (pz > gateFor(r.simpleChoice) || Math.cos(playerCarGroup.rotation.y) < 0.9)) { refuseInput(); return; }
    if (direction === 'uturn' && !uturnFits(r)) { refuseInput(); return; }
    let choice = direction;
    if (!previews[choice] || r.simpleChoice === choice) choice = previews.straight ? 'straight' : null;
    if (choice === r.simpleChoice) return;
    if (choice && pz > gateFor(choice)) { refuseInput(); return; }
    const previous = r.simpleChoice;
    r.simpleChoice = choice;
    // An exit that cannot be driven from where the car is now (half-way into
    // another turn, or out in the oncoming lane) is refused: the car keeps
    // its route and the phone buzzes.
    if (!applyJunctionChoice(r, true)) { r.simpleChoice = previous; refuseInput(); return; }
    // A press that leads away from the task's manoeuvre is the player's own
    // decision: the hint stops insisting.
    const toward = [r.spec.maneuver];
    if (!toward.includes(choice)) r.simpleDeviated = true;
    if (choice === 'left' || choice === 'right' || choice === 'uturn') triggerBlinker(choice === 'right' ? 'right' : 'left');
  }

  // An arrow press that can change nothing any more (the exit is committed,
  // no lane to move to): Flutter answers with a short vibration.
  function refuseInput() {
    sendToFlutter({ event: 'input_refused' });
  }

  // Simple mode at a task junction: the exit chosen so far and, until the
  // player decides otherwise, the arrow that leads to the task's manoeuvre.
  // The car never turns by itself — the hint only points at the arrow.
  function reportExit(r) {
    let choice = null, hint = null;
    if (r && state.simpleSteering && r.phase === 'manual') {
      choice = r.simpleChoice || null;
      const task = r.spec.maneuver;
      if (r.simpleOpen && playerCarGroup.position.z <= r.simpleGate && !r.simpleDeviated &&
          ['left', 'right', 'uturn'].includes(task) && choice !== task && r.intersection.previews?.[task]) {
        // 'uturn' is shown on the left button (a U-turn icon).
        hint = task;
      }
    }
    const uturn = uturnOffered(r);
    const key = choice + '|' + hint + '|' + uturn;
    if (key === state.exitReported) return;
    state.exitReported = key;
    sendToFlutter({ event: 'exit_choice', choice, hint, uturn });
  }

  // The first metres of a planned route keep the whole car on the road.
  function pathDrivable(path) {
    const length = path.getLength();
    for (let d = 0.5; d <= Math.min(length, 8); d += 0.5) {
      const u = d / length, tangent = path.getTangentAt(u);
      if (!playerOnRoad(path.getPointAt(u), Math.atan2(tangent.x, tangent.z))) return false;
    }
    return true;
  }

  // Plans the route for the chosen exit from where the car is. With check,
  // a route that would put the car on a kerb is not taken (returns false).
  function applyJunctionChoice(r, check = false) {
    const choice = r.simpleChoice;
    const roundabout = r.intersection.situation.geometry === 'roundabout';
    const car = playerCarGroup, start = car.position.clone();
    const heading = new THREE.Vector3(Math.sin(car.rotation.y), 0, Math.cos(car.rotation.y));
    if (!choice || (choice === 'straight' && !roundabout && !r.spec.paths?.straight)) {
      // Straight on: back to the centre of the lane the car is in (it may be
      // half-way into a turn the player changed their mind about).
      const z = r.intersection.centerZ, side = start.x < 0 ? -1 : 1;
      const laneX = side * (Math.abs(start.x) > 3.6 ? 5.4 : 1.8);
      const zA = Math.max(start.z + 10, z + 2), zB = Math.max(start.z + 24, z + 18);
      const path = new THREE.CubicBezierCurve3(start, start.clone().addScaledVector(heading, 4),
        new THREE.Vector3(laneX, 0, zA), new THREE.Vector3(laneX, 0, zB));
      if (check && !pathDrivable(path)) return false;
      state.autoPath = planPath(path);
      return true;
    }
    const { points, exitYaw } = maneuverPoints(r, choice, start);
    // Approach points the car has already passed would send it backwards.
    // Nor any closer than the run-out along the current heading added next
    // (2.5 m), or the curve would loop back towards the kerb.
    while (points.length > 3 && points[1].z < start.z + 3.5 && Math.abs(points[1].x - start.x) < 2.5) points.splice(1, 1);
    // Run out straight along the exit road so the car leaves square to it.
    const last = points[points.length - 1], out = new THREE.Vector3(Math.sin(exitYaw), 0, Math.cos(exitYaw));
    points.push(last.clone().addScaledVector(out, 8), last.clone().addScaledVector(out, 20));
    // Leave along the car's current heading (no snap when the choice changes
    // with the car already moving), shorter or not at all near a kerb.
    let path = null;
    for (const lead of [2.5, 1.2, 0]) {
      const withLead = lead ? [points[0], start.clone().addScaledVector(heading, lead), ...points.slice(1)] : points;
      path = curve(withLead);
      if (pathDrivable(path)) break;
      if (!lead && check) return false;
    }
    state.autoPath = planPath(path);
    return true;
  }

  // «Простое управление»: the wheel turns only inside a junction (after the
  // answer) or in reverse; elsewhere an arrow means the neighbouring lane.
  function freeWheel() {
    return !state.simpleSteering;
  }

  function applySteeringAssist(dt) {
    if (state.steering || state.autoPath || state.resolution || state.speed < 1.5) return;
    // Follow the widening carriageway before its median, rather than steering
    // toward the ordinary two-lane centre inside the new grass separator.
    const approach=state.intersections.find(it=>(it.situation.geometry==='divided_main'||it.situation.geometry==='motorway_parallel'||(it.situation.mainWidth>8.4&&it.situation.playerStartX!==undefined)) &&
      playerCarGroup.position.z>=it.centerZ-34 && playerCarGroup.position.z<=it.stopZ+.2);
    if(approach && Math.cos(playerCarGroup.rotation.y)>.85 && playerCarGroup.position.x<0 && state.laneChangeX==null) {
      const car=playerCarGroup,z=car.position.z;
      const lane=q=>-1.8+((approach.situation.playerStartX??-4.1)+1.8)*THREE.MathUtils.smoothstep(q-approach.centerZ,-26,-14);
      if(state.simpleSteering) {
        const points=[car.position.clone()];
        for(let q=z+1;q<approach.stopZ;q+=1)points.push(new THREE.Vector3(lane(q),0,q));
        points.push(new THREE.Vector3(lane(approach.stopZ+1),0,approach.stopZ+1));
        state.autoPath=planPath(curve(points));return;
      }
      const target=new THREE.Vector3(lane(z+3),0,z+3);
      const wanted=Math.atan2(target.x-car.position.x,target.z-car.position.z);
      const err=Math.atan2(Math.sin(wanted-car.rotation.y),Math.cos(wanted-car.rotation.y));
      car.rotation.y+=err*Math.min(1,dt*5);return;
    }
    const frame=curvedRoadFrame();
    if(frame) {
      const car=playerCarGroup,sign=Math.cos(car.rotation.y-frame.yaw)<0?-1:1;
      const axis=frame.yaw+(sign<0?Math.PI:0);
      const err=Math.atan2(Math.sin(axis-car.rotation.y),Math.cos(axis-car.rotation.y));
      if(Math.abs(err)>.45)return;
      const target=state.laneChangeX!=null&&state.curveLaneTarget!=null?state.curveLaneTarget:
        (frame.offset*sign>.85?1.8*sign:-1.8*sign);
      if(state.laneChangeX!=null&&Math.abs(frame.offset-target)<.12){state.laneChangeX=null;state.curveLaneTarget=null;}
      if(state.simpleSteering) {
        planLaneCurve(frame.pointAt(target,frame.local.z).x);return;
      }
      // Feed forward the road's curvature; lateral correction then has only
      // to remove drift rather than discovering each bend late.
      const slope=frame.data.slopeAt(frame.local.z),dz=state.speed*sign/Math.sqrt(1+slope*slope);
      const rate=Math.atan(frame.data.slopeAt(frame.local.z+.5))-Math.atan(frame.data.slopeAt(frame.local.z-.5));
      const pull=THREE.MathUtils.clamp((target-frame.offset)*.2*sign,-.25,.25);
      car.rotation.y+=rate*dz*dt+(err+pull)*Math.min(1,dt*4);
      return;
    }
    if (state.simpleSteering && state.laneChangeX == null) {
      // Simple mode keeps the car exactly on a lane centre: any leftover
      // offset (after a junction, a nudge) is taken out with a short curve.
      const x = playerCarGroup.position.x, yaw = playerCarGroup.rotation.y;
      const axis = Math.cos(yaw) < 0 ? Math.PI : 0;
      const off = Math.atan2(Math.sin(axis - yaw), Math.cos(axis - yaw));
      const lane = nearestLaneX(x);
      if (Math.abs(off) < 0.3 && (Math.abs(lane - x) > 0.08 || Math.abs(off) > 0.01)) {
        state.laneChangeX = lane;
        planLaneCurve(lane);
        return;
      }
    }
    const car = playerCarGroup, x = car.position.x;
    if (Math.abs(x) > 16) return;
    const back = Math.cos(car.rotation.y) < 0;
    const axis = back ? Math.PI : 0;
    const err = Math.atan2(Math.sin(axis - car.rotation.y), Math.cos(axis - car.rotation.y));
    if (Math.abs(err) > 0.45) return; // a deliberate turn: leave it alone
    // Nearest lane centre (driver's right is -X going forward).
    // A tapped lane change («простое управление») steers to the chosen lane,
    // otherwise the car settles into the nearest one.
    const change = state.laneChangeX;
    if (change != null && Math.abs(change - x) < 0.12) state.laneChangeX = null;
    const lane = state.laneChangeX ?? nearestLaneX(x);
    const pull = (state.laneChangeX != null
      ? THREE.MathUtils.clamp((lane - x) * 0.35, -0.32, 0.32)
      : THREE.MathUtils.clamp((lane - x) * 0.05, -0.06, 0.06)) * (back ? -1 : 1);
    const target = err + pull;
    car.rotation.y += target * Math.min(1, dt * (state.laneChangeX != null ? 4.5 : 1.8));
  }

  // Simple steering through a junction: the car slows for the curve ahead
  // like a driver would (a turn at 30-35 km/h, a U-turn at ~25), instead of
  // sweeping round at the full town speed with the gas held.
  function curveSpeedLimit(ap) {
    // braking: the coast-down rate integrateDriving applies with the gas held.
    const lateral = 18, braking = 4;
    let limit = Infinity;
    const at = s => { const t = ap.path.getTangentAt(Math.min(1, s / ap.length)); return Math.atan2(t.x, t.z); };
    for (let d = 0; d <= 30 && ap.s + d < ap.length; d += 1) {
      const a = at(ap.s + d), b = at(ap.s + d + 1);
      const bend = Math.abs(Math.atan2(Math.sin(b - a), Math.cos(b - a)));
      if (bend < 1e-3) continue;
      limit = Math.min(limit, Math.sqrt(lateral / bend + 2 * braking * d));
    }
    return Math.max(5.5, limit);
  }

  function integrateDriving(dt, limit = state.maxSpeed) {
    applySteeringAssist(dt);
    if (state.autoPath && state.resolution) limit = Math.min(limit, curveSpeedLimit(state.autoPath));
    // Brake: firm deceleration while moving; from a standstill it becomes
    // reverse gear (slow, negative speed). Gas is ignored while braking.
    if (state.isBraking) {
      if (state.speed > 0.05) state.speed = Math.max(0, state.speed - dt * 30);
      else state.speed = Math.max(-4, state.speed - dt * 5);
    } else if (state.speed < 0) {
      state.speed = Math.min(0, state.speed + dt * 12);
    } else if (state.speed > limit + 0.01) {
      // Above the limit in force (it just dropped): coast down, do not snap.
      state.speed = Math.max(limit, state.speed - dt * (state.isAccelerating ? 4 : 22));
    } else {
      state.speed = state.isAccelerating ? Math.min(limit, state.speed + dt * 9) : Math.max(0, state.speed - dt * 22);
    }
    const steps = Math.max(1, Math.ceil(Math.abs(state.speed) * dt / 0.15));
    let curbContact = false;
    for (let i = 0; i < steps; i++) {
      const before = playerCarGroup.position.clone(), oldYaw = playerCarGroup.rotation.y;
      const step = state.speed * dt / steps;
      // Slow steering remains available when the nose is pressed against a curb.
      // In reverse the rear swings the other way, as on a real car.
      if (state.steering && !freeWheel()) state.steering = 0;
      playerCarGroup.rotation.y += (state.steering || 0) * Math.sign(state.speed || 1) *
        Math.min(1.8, Math.max(state.isAccelerating ? 1 : 0, Math.abs(state.speed)) * 0.32) /
        // Softer at speed: a held arrow does not throw the car across the road.
        (1 + Math.max(0, Math.abs(state.speed) - 8) * 0.04) * dt / steps;
      let desiredYaw = playerCarGroup.rotation.y;
      let dx = Math.sin(desiredYaw) * step, dz = Math.cos(desiredYaw) * step;
      const ap = state.autoPath;
      // Reversing drops the planned move; the junction exit is planned again
      // from the new spot once the car rolls forward.
      if (ap && step < 0) { state.autoPath = null; state.replanExit = true; }
      if (step < 0 && state.simpleSteering) {
        // «Простое управление»: reverse retraces the way the car came, so it
        // stays in its lane; past the recorded trail it backs straight.
        const trail = state.trail || [];
        let remaining = -step, x = before.x, z = before.z, yaw = oldYaw;
        while (remaining > 1e-4 && trail.length) {
          const t = trail[trail.length - 1], d = Math.hypot(t.x - x, t.z - z);
          const turn = Math.atan2(Math.sin(t.yaw - yaw), Math.cos(t.yaw - yaw));
          if (d <= remaining) { x = t.x; z = t.z; yaw += turn; remaining -= d; trail.pop(); }
          else { const k = remaining / d; x += (t.x - x) * k; z += (t.z - z) * k; yaw += turn * k; remaining = 0; }
        }
        x -= Math.sin(yaw) * remaining; z -= Math.cos(yaw) * remaining;
        desiredYaw = yaw; playerCarGroup.rotation.y = yaw;
        dx = x - before.x; dz = z - before.z;
      } else if (ap && step > 0) {
        // «Простое управление»: the car rides the planned curve exactly.
        ap.s = Math.min(ap.length, ap.s + step);
        const t = ap.s / ap.length, point = ap.path.getPointAt(t), tangent = ap.path.getTangentAt(t);
        const yaw = Math.atan2(tangent.x, tangent.z);
        desiredYaw = oldYaw + Math.atan2(Math.sin(yaw - oldYaw), Math.cos(yaw - oldYaw));
        playerCarGroup.rotation.y = desiredYaw;
        dx = point.x - before.x; dz = point.z - before.z;
        if (ap.s >= ap.length) state.autoPath = null;
      }
      playerCarGroup.position.x += dx; playerCarGroup.position.z += dz;
      if (!playerOnRoad()) {
        curbContact = true;
        // Resolve the blocked normal component while preserving tangential travel.
        const candidates = [[dx, 0, desiredYaw], [0, dz, desiredYaw]];
        // Small lateral separation permits steering AWAY from a curb at rest.
        const correction = Math.min(0.08, dt / steps * 1.8);
        candidates.push([correction, dz, desiredYaw], [-correction, dz, desiredYaw],
          [dx, correction, desiredYaw], [dx, -correction, desiredYaw],
          [dx, 0, oldYaw], [0, dz, oldYaw]);
        let supported = false;
        for (const [x, z, yaw] of candidates) {
          playerCarGroup.position.copy(before).add(new THREE.Vector3(x, 0, z));
          playerCarGroup.rotation.y = yaw;
          if (playerOnRoad()) { supported = true; break; }
        }
        if (!supported) { playerCarGroup.position.copy(before); playerCarGroup.rotation.y = oldYaw; }
      }
      const obstacle = Math.abs(step) > 0.0001
        ? state.actors.find(a => !a.done && !a.fall && footprintsOverlap(playerFootprint(), actorFootprint(a), 0.025))
        : null;
      if (obstacle) {
        const previousPlayer = { p: before, yaw: oldYaw,
          halfWidth: playerCarGroup.userData.halfWidth, halfLength: playerCarGroup.userData.halfLength };
        const other = actorFootprint(obstacle);
        const wasOverlapping = footprintsOverlap(previousPlayer, other, 0.025);
        const separating = playerCarGroup.position.distanceTo(other.p) > before.distanceTo(other.p) + 0.002;
        const stationary = obstacle.crashed;
        if (stationary && !obstacle.fall && step > 0) {
          // A car left standing after a crash never traps the player (and is
          // no new ДТП): the gas nudges it out of the way at walking pace.
          // Mostly sideways, off the player's line, so the way clears
          // quickly instead of the wreck being shoved down the road.
          const at = obstacle.mesh.getWorldPosition(new THREE.Vector3());
          const forward = new THREE.Vector3(dx, 0, dz).normalize(), right = new THREE.Vector3(forward.z, 0, -forward.x);
          const side = Math.sign(at.clone().sub(before).dot(right)) || Math.sign(at.x) || 1;
          const target = at.addScaledVector(forward.multiplyScalar(0.35).addScaledVector(right, side).normalize(), Math.hypot(dx, dz) * 1.6);
          obstacle.mesh.position.copy(obstacle.mesh.parent.worldToLocal(target));
          state.speed = Math.min(state.speed, 1.5);
          continue;
        }
        if (!wasOverlapping && !(stationary && Math.abs(state.speed) < 3)) {
          playerCarGroup.position.copy(before); playerCarGroup.rotation.y = oldYaw;
          handleCollision(obstacle, 'collision:' + obstacle.config.id);
          break;
        }
        if (!wasOverlapping || !separating) {
          // Touching a parked crash participant at walking pace, or pushing
          // deeper into an existing contact, is not a
          // new ДТП: the move is simply blocked (like a curb). Steering out of
          // it stays possible so the run never freezes.
          const blocked = [[0, 0, desiredYaw], [dx, 0, desiredYaw], [0, dz, desiredYaw]].every(([x, z, yaw]) => {
            playerCarGroup.position.copy(before).add(new THREE.Vector3(x, 0, z));
            playerCarGroup.rotation.y = yaw;
            return !playerOnRoad() || footprintsOverlap(playerFootprint(), other, 0.025) ||
              playerCarGroup.position.distanceTo(other.p) + 0.002 < before.distanceTo(other.p);
          });
          if (blocked) { playerCarGroup.position.copy(before); playerCarGroup.rotation.y = oldYaw; }
          if (wasOverlapping && obstacle.crashed && !obstacle.knock) separateCrashedActor(obstacle);
          state.speed = Math.sign(state.speed) * Math.min(Math.abs(state.speed), 1.5);
          break;
        }
      }
      if (state.speed > 0) state.distanceTraveled += playerCarGroup.position.distanceTo(before);
      if (step > 0) {
        // The way the car came (for reversing in «Простое управление»).
        const trail = state.trail || (state.trail = []), p = playerCarGroup.position, last = trail[trail.length - 1];
        if (!last || Math.hypot(p.x - last.x, p.z - last.z) > 0.25) {
          trail.push({ x: p.x, z: p.z, yaw: playerCarGroup.rotation.y });
          if (trail.length > 600) trail.shift();
        }
      }
    }
    if (curbContact) {
      drivingFault('offroad', 'offroad');
      state.speed = Math.max(-2, Math.min(state.speed, 4));
      if (state.curbClearTime !== 0 && Math.abs(state.speed) > 1.5) gameAudio?.scrapeHit();
      state.curbClearTime = 0;
    } else {
      state.curbClearTime = (state.curbClearTime || 0) + dt;
      if (state.curbClearTime > 0.6) (state.resolution ? state.resolution.faults : state.driveFaults).delete('offroad');
    }
  }

  // Retired streets are cut off with clipping planes, not removed at once:
  // whatever lies beyond the cut is not drawn — and must not be felt either
  // (a median, a hump, a cone of a street that is no longer there).
  function clippedAway(material, point) {
    const m = Array.isArray(material) ? material[0] : material;
    return !!m?.clippingPlanes?.some(plane => plane.distanceToPoint(point) < -0.01);
  }
  // The first drawn part of an event's own scenery (not a road user), whose
  // material carries the cuts made to the whole group.
  function clipProbe(group) {
    let probe = null;
    group.traverse(o => {
      if (probe || !o.isMesh || !o.material) return;
      for (let a = o; a && a !== group; a = a.parent) if (a.userData.actor || a.userData.sceneryObject) return;
      probe = o;
    });
    return probe;
  }

  function refreshRoadBounds() {
    window.PDD_ROADS.invalidate();
    scene.updateMatrixWorld(true);
    state.roadBounds = [];
    state.curvedRoads = [];
    state.roadSegments.forEach(seg=>seg.traverse(group=>{
      if(group.userData.centerline)state.curvedRoads.push({group,data:group.userData.centerline,inverse:group.matrixWorld.clone().invert(),probe:clipProbe(group)});
    }));
    // Kerbed islands over asphalt (a median): their own exact shape.
    state.noRoad = [];
    state.roadSegments.forEach(seg => seg.traverse(obj => {
      if (obj.userData.noRoad && obj.visible) state.noRoad.push({ test: obj.userData.noRoad, inverse: obj.matrixWorld.clone().invert(), mesh: obj });
    }));
    state.roadSegments.forEach(seg => seg.traverse(obj => {
      if (obj.userData.surface === 'road') state.roadBounds.push({
        box: new THREE.Box3().setFromObject(obj), material: obj.material,
        // A rounded corner is road only outside its kerb curve.
        fillet: obj.userData.fillet && { center: obj.userData.fillet.center.clone().applyMatrix4(obj.matrixWorld), r: obj.userData.fillet.r },
        containsRoad: obj.userData.containsRoad,
        inverse: obj.userData.containsRoad && obj.matrixWorld.clone().invert(),
      });
    }));
  }

  function curvedRoadFrame(point=playerCarGroup.position) {
    for(const {group,data,inverse,probe} of state.curvedRoads||[]) {
      const local=point.clone().applyMatrix4(inverse);
      if(local.z<data.from||local.z>data.to||Math.abs(local.x-data.centerAt(local.z))>6||
        (probe&&clippedAway(probe.material,point)))continue;
      const tangent=new THREE.Vector3(data.slopeAt(local.z),0,1).transformDirection(group.matrixWorld);
      return {data,group,local,offset:local.x-data.centerAt(local.z),yaw:Math.atan2(tangent.x,tangent.z),
        pointAt:(offset,z)=>new THREE.Vector3(data.centerAt(z)+offset,0,z).applyMatrix4(group.matrixWorld),
        offsetOf:x=>new THREE.Vector3(x,0,point.z).applyMatrix4(inverse).x-data.centerAt(local.z)};
    }
    return null;
  }

  function roadSupports(point) {
    if ((state.noRoad || []).some(({ test, inverse, mesh }) => !clippedAway(mesh.material, point) && test(point.clone().applyMatrix4(inverse)))) return false;
    return (state.roadBounds || []).some(({box, material, fillet, containsRoad, inverse}) =>
      point.x >= box.min.x - 0.1 && point.x <= box.max.x + 0.1 &&
      point.z >= box.min.z - 0.1 && point.z <= box.max.z + 0.1 &&
      (!fillet || Math.hypot(point.x - fillet.center.x, point.z - fillet.center.z) >= fillet.r - 0.05) &&
      (!containsRoad || containsRoad(point.clone().applyMatrix4(inverse))) &&
      (material.clippingPlanes || []).every(plane => plane.distanceToPoint(point) >= -0.01));
  }

  function playerOnRoad(at = playerCarGroup.position, yaw = playerCarGroup.rotation.y) {
    for (const x of [-playerCarGroup.userData.halfWidth, playerCarGroup.userData.halfWidth])
      for (const z of [-playerCarGroup.userData.halfLength, playerCarGroup.userData.halfLength]) {
        const corner = new THREE.Vector3(x, 0, z).applyAxisAngle(new THREE.Vector3(0, 1, 0), yaw).add(at);
        if (!roadSupports(corner)) return false;
      }
    return true;
  }

  function updatePlayerMovement(dt) {
    if (state.pendingVehicle && Math.abs(state.speed) <= 0.1) selectVehicle(...state.pendingVehicle);
    if (state.isAtSituation) { state.speed = 0; return; }
    if (state.motorwayEndZ != null && playerCarGroup.position.z > state.motorwayEndZ) {
      state.motorwayEndZ = null;
      if (state.speedLimitKmH === 110) state.speedLimitKmH = null;
    }
    if (state.driveRecovery > 0) {
      state.driveRecovery = Math.max(0, state.driveRecovery - dt);
      if (!state.driveRecovery) {
        state.driveFaults.clear();
        sendToFlutter({ event: 'maneuver_ready' });
      }
      return;
    }
    const active = state.intersections.find(it => it.stopZ + 3 > playerCarGroup.position.z);
    state.activeIntersection = active || null;
    let limit = state.maxSpeed;
    if (active && Math.cos(playerCarGroup.rotation.y) > 0.2) {
      const distance = active.stopZ - playerCarGroup.position.z;
      limit = Math.min(limit, Math.sqrt(Math.max(0, 2 * 8 * distance)));
    }
    if (Math.cos(playerCarGroup.rotation.y) > 0.2) limit = roadEventLimit(playerCarGroup.position.z, limit);
    const contactsBefore = playerContacts();
    integrateDriving(dt, limit);
    updateBodyOverHumps();
    if (state.driveRecovery > 0) return;
    const laneFrame=curvedRoadFrame();
    state.currentLaneOffset = laneFrame?laneFrame.offset:playerCarGroup.position.x;
    const oneWay = oneWayStatus();
    if (oneWay) updateLaneViolation(dt, false, oneWay === 'against');
    else {
      const inOncomingLane = Math.cos(playerCarGroup.rotation.y-(laneFrame?.yaw||0)) * state.currentLaneOffset > 0.85;
      updateLaneViolation(dt, inOncomingLane && !roadOvertakeAllowedAt(playerCarGroup.position.z));
    }
    for (const actor of state.actors) {
      if (actor.done || actor.fall) continue;
      if (footprintsOverlap(playerFootprint(), actorFootprint(actor))) {
        if (contactsBefore.has(actor)) { if (actor.crashed && !actor.knock) separateCrashedActor(actor); continue; }
        if (actor.crashed) continue; // a wreck being nudged aside, no new ДТП
        handleCollision(actor, 'collision:' + actor.config.id); return;
      }
    }
    if (Math.abs(Math.sin(playerCarGroup.rotation.y-(laneFrame?.yaw||0))) < 0.2 && Math.abs(state.currentLaneOffset) < 2.5) {
      state.lastSafePosition.copy(playerCarGroup.position);
      state.lastSafeYaw = playerCarGroup.rotation.y;
    }
    const road = state.roadEvent;
    if (road && road.phase === 'approach' && road.stopZ !== undefined &&
        road.stopZ - playerCarGroup.position.z <= 0.18 && road.stopZ + 3 > playerCarGroup.position.z &&
        Math.cos(playerCarGroup.rotation.y) > 0.2) {
      startRoadQuestion();
      return;
    }
    if (active && active.stopZ - playerCarGroup.position.z <= 0.18) {
      if (active.situation.playerStartX !== undefined) playerCarGroup.position.x = active.situation.playerStartX;
      state.speed = 0;
      state.isAccelerating = false;
      state.steering = 0; state.laneChangeX = null; state.autoPath = null;
      state.isAtSituation = true;
      sendToFlutter({ event: 'approach_situation', situation: active.situation });
    }
  }

  let cameraLook = new THREE.Vector3(0, 0, 14), cameraHeading = 0, cameraViewSize = 42;
  function updateCamera(dt) {
    const question=questionCameraOpen();
    if(state.cameraQuestionActive && !question)resetQuestionCamera();
    state.cameraQuestionActive=question;
    if (state.viewportTarget) {
      const k = 1 - Math.exp(-4 * dt), v = state.viewportInsets, t = state.viewportTarget;
      v.top += (t.top - v.top) * k; v.bottom += (t.bottom - v.bottom) * k;
    }
    const height = container.clientHeight || window.innerHeight;
    const width = container.clientWidth || window.innerWidth;
    if (width <= 0 || height <= 0) return;
    state.intersections.forEach(it => {
      it.guide.visible = !it.situation.hideGuide && it === state.activeIntersection && Math.abs(playerCarGroup.position.z - it.centerZ) < 55;
    });
    state.orbitYaw = state.attract ? (state.orbitYaw || 0) : (state.orbitYaw || 0) * Math.exp(-4 * dt);
    let desiredYaw = playerCarGroup.rotation.y + (state.orbitYaw || 0);
    let delta = Math.atan2(Math.sin(desiredYaw - cameraHeading), Math.cos(desiredYaw - cameraHeading));
    cameraHeading += delta * (1 - Math.exp(-3 * dt));
    const forward = new THREE.Vector3(Math.sin(cameraHeading), 0, Math.cos(cameraHeading));
    const focus = playerCarGroup.position.clone();
    let lookAhead = 10;
    let desiredViewSize = 42;
    const roadQuestion = state.roadEvent?.phase === 'question' ? state.roadEvent : null;
    if (roadQuestion) {
      // Frame the player, the signs and the traffic of this stretch, not the
      // junction 200 m ahead that state.activeIntersection already points at.
      const ev = roadQuestion;
      const boxes = ev.actors.map(a => {
        const b = new THREE.Box3().setFromObject(a.mesh);
        // The photograph crops the freight train. Frame the crossing, not all wagons.
        if (a.config.type === 'train') b.intersect(new THREE.Box3(new THREE.Vector3(-12,0,ev.crossingZ-5),new THREE.Vector3(12,6,ev.crossingZ+8)));
        return b;
      });
      if (ev.rail && ev.scene.railway.z < 65) boxes.push(new THREE.Box3(new THREE.Vector3(-8,0,ev.crossingZ-12),new THREE.Vector3(8,4.5,ev.crossingZ+8)));

      // Frame answer evidence, not long marking meshes or distant zone-end signs.
      ev.group.children.filter(o => o.userData.questionEvidence && !o.userData.actor && o !== ev.guide && o.position.z <= ev.stopZ + 60)
        .forEach(o => boxes.push(new THREE.Box3().setFromObject(o)));
      if (ev.guide?.userData.questionEvidence) {
        const b = new THREE.Box3().setFromObject(ev.guide);
        if(ev.kind === 'temporary_bypass') b.max.z=Math.min(b.max.z,ev.stopZ+64);
        boxes.push(b);
      }
      const minX = Math.min(-6, ...boxes.map(b => b.min.x)) - 1;
      const maxX = Math.max(6, ...boxes.map(b => b.max.x)) + 1;
      if (ev.junctionZ !== undefined && ev.junctionZ < ev.stopZ + 65) {
        boxes.push(new THREE.Box3(new THREE.Vector3(-14, 0, ev.junctionZ - 7), new THREE.Vector3(14, 0, ev.junctionZ + 7)));
      }
      // Tight on what the question is about (a car and a sign next to it
      // need no 40 m of road): the view only grows for evidence far ahead.
      const minZ = Math.min(playerCarGroup.position.z - 4, ...boxes.map(b => b.min.z - 2));
      const maxZ = Math.min(ev.stopZ + 60, Math.max(ev.stopZ + 8, ...boxes.map(b => b.max.z + b.max.y * 1.05))) + 2;
      const visibleFraction = Math.max(0.25, (height - state.viewportInsets.top - state.viewportInsets.bottom) / height);
      desiredViewSize = Math.max(26, (maxX - minX) / (width / height), (maxZ - minZ) * 0.69 / visibleFraction);
      focus.set((minX + maxX) / 2, 0, (minZ + maxZ) / 2);
      lookAhead = 0;
    } else if (state.isAtSituation && state.activeIntersection && state.resolution?.phase !== 'manual') {
      const intersection = state.activeIntersection;
      const bounds = intersection.actors.map(a => a.viewBounds);
      intersection.seg.children.filter(o => o.userData.trajectoryLabel || o.userData.questionEvidence).forEach(o => bounds.push(new THREE.Box3().setFromObject(o)));
      const minX = Math.min(-7, ...bounds.map(b => b.min.x)) - 1.5;
      const maxX = Math.max(7, ...bounds.map(b => b.max.x)) + 1.5;
      const minZ = Math.min(playerCarGroup.position.z - 2.5, intersection.centerZ - 8, ...bounds.map(b => b.min.z)) - 1.5;
      // At this camera elevation model/badge height contributes ~1m of forward
      // projection per metre of height. Reserve it above the roof, under the HUD.
      const maxZ = Math.max(intersection.centerZ + 8, ...bounds.map(b => b.max.z + b.max.y * 1.05)) + 2;
      const visibleFraction = Math.max(0.25, (height - state.viewportInsets.top - state.viewportInsets.bottom) / height);
      desiredViewSize = Math.max(42, (maxX - minX) / (width / height), (maxZ - minZ) * 0.69 / visibleFraction);
      focus.set((minX + maxX) / 2, 0, (minZ + maxZ) / 2);
      lookAhead = 0;
    }
    const alpha = 1 - Math.exp(-5 * dt);
    const questionFrameSize=desiredViewSize;
    desiredViewSize *= state.userZoom || 1;
    cameraViewSize += (desiredViewSize - cameraViewSize) * alpha;
    if(question){
      // The initial uncovered question frame is the inspection boundary.
      // Zooming in reveals room to pan inside it; zooming back out removes it.
      const room=Math.max(0,Math.min(questionFrameSize-cameraViewSize,questionFrameSize*(1-(state.userZoom||1))));
      const visibleFraction=Math.max(.25,(height-state.viewportInsets.top-state.viewportInsets.bottom)/height);
      state.questionCameraBounds={right:new THREE.Vector3(forward.z,0,-forward.x),forward:forward.clone(),
        side:room*width/height/2,along:room*visibleFraction/(2*.69)};
      const previous=state.questionCameraPan.clone();constrainQuestionPan(state.questionCameraPan);
      const correction=state.questionCameraPan.clone().sub(previous);
      cameraLook.add(correction);camera.position.add(correction);
    }
    camera.left = -cameraViewSize * width / height / 2;
    camera.right = -camera.left;
    camera.top = cameraViewSize / 2; camera.bottom = -camera.top;
    camera.updateProjectionMatrix();
    // Camera framing can zoom out on a short screen. Keep the ticket letters
    // readable instead of shrinking them into dots under a tall answer card.
    for (const group of [state.activeIntersection?.seg, state.roadEvent?.guide]) {
      group?.children.forEach(o => {
        if (o.userData.trajectoryLabel) o.scale.setScalar(Math.max(1.5, 24 * cameraViewSize / height));
      });
    }
    // Place the scene at the centre of the ACTUAL uncovered viewport, including
    // large text / tall answer sheets, rather than the centre behind the sheet.
    const close=!question&&!state.attract?Math.max(0,(1-(state.userZoom||1))/(1-ZOOM_MIN)):0;
    const cameraHeight=42-20*close,behind=44+8*close;
    if(close)lookAhead+=5*close;
    const projection=Math.max(.3,cameraHeight/Math.hypot(cameraHeight,behind));
    const offset = (state.viewportInsets.bottom - state.viewportInsets.top) / height * cameraViewSize / (2 * projection);
    if(question)focus.add(state.questionCameraPan);
    const desiredLook = focus.clone().addScaledVector(forward, lookAhead - offset);
    const desiredPos = desiredLook.clone().addScaledVector(forward, -behind);
    desiredPos.y = cameraHeight;
    // The frustum already eases the zoom. During inspection the pose must
    // match that frustum, or a second easing would drift the gesture anchor.
    const poseAlpha=question&&state.questionCameraInspecting?1:alpha;
    cameraLook.lerp(desiredLook, poseAlpha);
    camera.position.lerp(desiredPos, poseAlpha);
    camera.lookAt(cameraLook);
    if(question&&state.questionZoomAnchor){
      camera.updateMatrixWorld(true);
      const anchor=state.questionZoomAnchor,ray=new THREE.Raycaster();ray.setFromCamera(anchor.screen,camera);
      const point=ray.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0,1,0),0),new THREE.Vector3());
      if(point){
        const delta=anchor.point.clone().sub(point);delta.y=0;
        const previous=state.questionCameraPan.clone();
        state.questionCameraPan.add(delta);constrainQuestionPan(state.questionCameraPan);
        const allowed=state.questionCameraPan.clone().sub(previous);
        if(allowed.distanceTo(delta)>1e-5)state.questionZoomAnchor=null;
        cameraLook.add(allowed);camera.position.add(allowed);camera.lookAt(cameraLook);
      }
    }
    // Free steering can put scenery between the camera and the car. Fade only
    // those buildings in front of the car; never hide the road itself. The
    // camera is orthographic: every line of sight runs along its direction,
    // so the check goes from the car (its sills and its roof) back towards
    // the camera — not to the camera's position, which is off to one side
    // whenever the car is not in the middle of the frame.
    const towardsCamera = camera.getWorldDirection(new THREE.Vector3()).negate();
    const car = playerCarGroup.position;
    const sights = [0.4, 1.5].map(y => new THREE.Ray(new THREE.Vector3(car.x, y, car.z), towardsCamera));
    state.occluders.forEach(building => {
      if (!building.parent) return;
      const bounds = new THREE.Box3().setFromObject(building);
      const faded = bounds.distanceToPoint(car) < 90 && sights.some(ray => ray.intersectsBox(bounds));
      building.traverse(part => {
        if (!part.material) return;
        part.material.transparent = faded;
        part.material.opacity = faded ? 0.14 : 1;
        part.material.depthWrite = !faded;
      });
    });
    sunTarget.position.copy(cameraLook);
    dirLight.position.copy(cameraLook).add(new THREE.Vector3(12, 70, -7));
  }

  function onWindowResize() {
    const width = container.clientWidth || window.innerWidth;
    const height = container.clientHeight || window.innerHeight;
    if (width <= 0 || height <= 0) return;
    const aspect = width / height;
    const viewSize = 42;
    camera.left = -viewSize * aspect / 2;
    camera.right = viewSize * aspect / 2;
    camera.top = viewSize / 2;
    camera.bottom = -viewSize / 2;
    camera.updateProjectionMatrix();
    renderer.setSize(width, height);
  }

  function resetGame() {
    resetQuestionCamera();state.cameraQuestionActive=false;
    state.roadSegments.forEach(disposeSegment);
    state.roadSegments = [];
    window.PDD_ROADS.reset();
    state.intersections = [];
    state.actors = [];
    state.ambient = [];
    state.occluders = [];
    state.district = 0;
    currentCorridor = null;
    state.exitRoad = null;
    state.driveFaults.clear();
    state.driveRecovery = 0;
    state.lastSafePosition.set(-1.8, 0, 0);
    state.lastSafeYaw = 0;
    state.resolution = null;
    state.exitReported = undefined;
    state.junctionsDrawn = 0;
    state.regulatorAt = undefined;
    state.activeIntersection = null;
    state.roadEvent = null;
    state.roadTurn = 0;
    state.busBays = [];
    state.props = [];
    state.humps = []; state.blockers = [];
    state.flying = [];
    state.crews = [];
    state.sideJunction = null;
    state.oneWayAgainst = false;
    state.sky = null; state.weatherOverride = null; state.rain = 0; state.overcast = 0;
    state.speedZoneActive = false; state.carriedZoneEndZ = undefined;
    state.speedLimitKmH = null;
    state.speedingTime = 0;
    state.speedingPenalized = false;
    roadBag = [];
    state.currentSituation = null;
    state.speed = 0;
    state.distanceTraveled = 0;
    state.isAtSituation = false;
    state.isResolvingSituation = false;
    state.isAccelerating = false;
    state.isBraking = false;
    state.targetLane = 1;
    state.currentLaneOffset = state.targetLaneOffset = -1.8;
    state.curveLaneTarget = null;
    state.violationEpisode = 0;
    state.steering = 0; state.laneChangeX = null; state.autoPath = null; state.trail = [];
    state.pendingAnswer = null;
    state.blinker = null;
    state.hazard = 0;
    clearOncoming();
    situationIndex = 0;
    situationBag = [];
    playerCarGroup.position.set(-1.8, 0, 0);
    playerCarGroup.rotation.set(0, 0, 0);
    camera.position.set(0, 42, -36);
    cameraLook.set(0, 0, 14);
    cameraHeading = 0;
    cameraViewSize = 42;
    buildInitialTrack();
    telemetryElapsed = 0;
  }

  window.game = {
    releaseTraffic,
    setGas(isPressed) {
      if (isPressed) gameAudio?.unlock();
      if (state.attract) { state.isAccelerating = false; return; }
      state.isAccelerating = !state.paused && !state.driveRecovery && (!state.isAtSituation || state.resolution?.phase === 'manual') && !state.resolution?.recovery && Boolean(isPressed);
    },
    setBrake(isPressed) {
      state.isBraking = !state.paused && !state.driveRecovery && (!state.isAtSituation || state.resolution?.phase === 'manual') && !state.resolution?.recovery && Boolean(isPressed);
    },
    // Signed-out visitors: a living street to look at (finger orbits the camera).
    setAttract(on) {
      state.attract = Boolean(on);
      if (!state.attract) {
        state.orbitYaw = 0;
        // The visitor is now a driver: clear the attract traffic before
        // the first metre so nothing is left sitting in the oncoming lane.
        state.actors.forEach(a => { if (a.config?.id?.startsWith('attract_')) { a.done = true; a.mesh.visible = false; } });
        (state.attractGroups || []).forEach(disposeSegment);
        state.attractGroups = [];
      }
    },
    // Garage reveal of a newly unlocked car; tap opens the door, finger spins.
    showReveal(id, paint) {
      if (!window.PDD_VEHICLES.specs[id]) return;
      if (reveal) window.game.hideReveal();
      state.isAccelerating = false;
      reveal = buildRevealScene(id, paint || null);
      updateReveal(0);
    },
    openReveal() { if (reveal && reveal.phase === 'closed') { reveal.phase = 'opening'; reveal.t = 0; gameAudio?.click(); } },
    // Start screen: the garage with the current car already out on its pad.
    showLobby(id, paint) {
      const vid = window.PDD_VEHICLES.specs[id] ? id : 'hatch';
      if (reveal) window.game.hideReveal();
      reveal = buildRevealScene(vid, paint || null);
      const r = reveal;
      r.phase = 'lobby';
      r.door.position.y = 4.3; r.door.children.forEach(slat => { slat.visible = false; });
      r.car.position.set(0, 0, -6.6);
      r.yaw = Math.PI + Math.PI / 2 - 0.5; r.car.rotation.y = r.yaw;
      updateReveal(0);
    },
    hideLobby() { if (reveal?.phase === 'lobby') window.game.hideReveal(); },
    // A finger drag on the start screen turns the car.
    lobbySpin(dx) { if (reveal?.phase === 'lobby') { reveal.yaw += dx * 0.012; reveal.spin = dx * 0.6; } },
    // Browsing cars on the start screen: the current car drives off one side
    // while the next one rolls in from the other. dir 1 = next (arrives from
    // the right of the screen), -1 = previous.
    lobbySwap(id, paint, dir = 1) {
      const r = reveal;
      if (!r || r.phase !== 'lobby' || !window.PDD_VEHICLES.specs[id]) { window.game.showLobby(id, paint); return; }
      if (r.swap) { r.scene.remove(r.swap.from); r.swap.to.position.x = 0; r.swap = null; }
      const next = window.PDD_VEHICLES.create(id, paint || null);
      next.position.set(-9 * dir, 0, -6.6); next.rotation.y = r.yaw;
      r.scene.add(next);
      r.swap = { from: r.car, to: next, dir, t: 0 };
      r.car = next;
    },
    hideReveal() {
      if (!reveal) return;
      // Vehicle/road texture maps belong to the shared caches, not this scene.
      const geometries = new Set(), materials = new Set(), maps = new Set();
      reveal.scene.traverse(o => { if (o.geometry) geometries.add(o.geometry); if (o.material) [].concat(o.material).forEach(m => materials.add(m)); });
      materials.forEach(m => { if (m.map && !m.map.userData?.pddVehicleShared && !m.map.userData?.pddRoadShared) maps.add(m.map); m.dispose(); });
      maps.forEach(t => t.dispose()); geometries.forEach(g => g.dispose());
      reveal.scene.background?.dispose();
      reveal = null;
      renderer.render(scene, camera);
    },
    thumbnail(id, paint) { try { return renderThumbnail(id, paint || null); } catch (_) { return ''; } },
    changeLane(direction) { changeLane(direction); },
    // The U-turn button of simple steering (shown only where one is allowed).
    chooseUturn() {
      const r = state.resolution;
      if (!r || r.phase !== 'manual' || r.recovery || !state.simpleSteering) { refuseInput(); return; }
      chooseJunctionExit('uturn');
    },
    setSimpleSteering(on) { state.simpleSteering = Boolean(on); },
    setSteering(direction) {
      const wanted = Math.sign(Number(direction) || 0);
      if (!freeWheel()) { state.steering = 0; return; } // simple mode: taps only (changeLane)
      state.steering = !state.paused && !state.driveRecovery && (!state.isAtSituation || state.resolution?.phase === 'manual') && !state.resolution?.recovery
        ? Math.max(-1, Math.min(1, Number(direction) || 0)) : 0;
      // The indicator comes on only for a deliberate hold (see updateBlinkers):
      // a quick tap to straighten the car does not blink.
      if (state.steering) state.laneChangeX = null;
      if (Math.sign(state.steering) !== Math.sign(state.steerHoldSide || 0)) { state.steerHold = 0; state.steerHoldSide = state.steering; }
    },
    switchLane,
    selectVehicle,
    // An answer that arrives while the engine is paused (the garage, a new
    // car's reveal, the app in the background) is kept and applied on
    // resume: dropped, it left the car waiting at the question for good.
    proceedAfterAnswer(isCorrect, situationId) {
      if (state.paused) { state.pendingAnswer = [isCorrect, situationId]; return; }
      resolveSituationAnimation(isCorrect, situationId);
    },
    setPaused(paused) {
      const next = Boolean(paused);
      if (next === state.paused) return;
      state.paused = next;
      // The planned move (a lane change, a turn) is kept: resumed, the car
      // carries on with it instead of going straight on.
      if (next) { state.isAccelerating = false; state.isBraking = false; state.steering = 0; }
      gameAudio?.setPaused(next);
      lastTime = null;
      if (!next && state.pendingAnswer) {
        const [isCorrect, situationId] = state.pendingAnswer;
        state.pendingAnswer = null;
        resolveSituationAnimation(isCorrect, situationId);
      }
    },
    // Overlays come and go (question card, pedals): the camera eases to the
    // new framing instead of jumping. The very first value is applied at once.
    setViewportInsets(insets) {
      const next = { top: Math.max(0, Number(insets.top) || 0), bottom: Math.max(0, Number(insets.bottom) || 0) };
      if (!state.viewportTarget) state.viewportInsets = { ...next };
      state.viewportTarget = next;
    },
    configure(config) {
      state.nativeControls = true;
      if (config.labels) Object.assign(state.labels, config.labels);
      // A first-time player sees clear weather for the whole session.
      state.firstRun = Boolean(config.firstRun);
      gameAudio?.setEnabled(config.soundEnabled !== false);
    },
    setTheme(isDark) {
      state.isDarkTheme = Boolean(isDark);
      applyWeather();
      renderer.render(scene, camera);
    },
    // Debug/testing: 'summer' | 'autumn' | 'winter', or null for the calendar.
    // Existing scenery is re-tinted; trees keep their colour until rebuilt.
    setSeason(kind) {
      currentSeason = SEASONS[kind] || SEASONS[seasonFromDate()];
      const sn = currentSeason;
      sendToFlutter({ event: 'season', season: seasonName() });
      scene.traverse(o => {
        const tag = o.material?.userData?.seasonal; if (!tag) return;
        if (tag === 'ground') o.material.color.setHex(sn.ground);
        else if (tag.startsWith('verge')) o.material.color.setHex(sn.verge[Number(tag[5])] || sn.ground);
        else if (tag === 'sidewalk') o.material.color.setHex(sn.sidewalk);
        else if (tag === 'roof') o.material.color.setHex(sn.roof || (Math.random() > 0.5 ? 0x8C4A3C : 0x5D6B75));
        else if (tag === 'canopy') o.material.color.setHex(sn.canopy[Math.floor(Math.random() * sn.canopy.length)]);
        else if (tag === 'birch') o.material.color.setHex(Math.random() < 0.7 ? sn.birch : sn.canopy[Math.floor(Math.random() * sn.canopy.length)]);
        else if (tag === 'water') o.material.color.setHex(sn.precipitation === 'snow' ? 0xD7E6EE : 0x6FA8C9);
      });
      state.weatherDirty = true;
    },
    // Debug/testing: force 'clear' | 'overcast' | 'rain', or null for the
    // automatic cycle.
    setWeather(kind) {
      state.weatherOverride = ['clear', 'overcast', 'rain'].includes(kind) ? kind : null;
      if (!state.sky) state.sky = { kind: 'clear', left: 0 };
      if (state.weatherOverride) { state.sky.kind = state.weatherOverride; state.sky.left = 1e9; }
      else state.sky.left = 0;
    },
    reset: resetGame,
    highlightMistake,
    clearMistakeHighlight
  };
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) window.game.setPaused(true);
  });

  // Run init on DOM ready
  window.addEventListener('error', () => sendToFlutter({ event: 'engine_error' }));
  window.addEventListener('unhandledrejection', () => sendToFlutter({ event: 'engine_error' }));
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();

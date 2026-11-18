# MotorX real car models

Drop one file per car in this folder, named after the car's id: `<id>.glb`
(e.g. `huracan.glb`, `g63.glb`, `civic.glb`). Any car without a file keeps its built-in shape,
so you can add them one at a time. Upload the whole folder to Netlify as before.

Car ids: civic corolla accord camry mx5 golf wrx wrangler f150 model3 mustang supra charger
corvette m3 gtr p911 plaid r8 g63 huracan f488 mclaren phantom chiron fiat500 beetle elantra
prius mazda3 altima mini crv rav4 outback odyssey hilux s2000 explorer (full list: the CARS array in index.html).

## Model requirements
- Format: binary glTF (.glb). Convert FBX/OBJ/blend with Blender (File > Export > glTF 2.0 > .glb).
- Orientation: car facing +Z (front toward +Z), upright (+Y up). If it faces the wrong way set "rot":180 in config.json.
- Real-world size is not needed: the game scales the car to fit the car's built-in length. Origin position does not matter.
- Keep each car under ~3-5 MB (apply Draco/meshopt compression, 40-80k triangles, textures 1024-2048px). Cars load only when selected.
- Material names the game recognises (set them in Blender):
  - body paint: a material named like "Paint", "CarPaint", "Body" -> gets the player's chosen colour
  - lights: "TailLight"/"Brake" -> red brake/tail light that reacts to braking; "HeadLight" -> headlamps
- Wheels: name each wheel part (tire, rim) with "wheel", "tire" or "rim" in the node name (Wheel_FL, Tire_RR, ...).
  Exactly 4 wheels (tire+rim of one corner are grouped automatically). They then spin and steer.
  Leave brake discs/calipers named "brake_disc"/"caliper" so they stay on the car.

## Optional models/config.json
{ "huracan": { "rot": 180, "length": 4.6, "y": 0.0, "paint": "carpaint|body", "wheel": "wheel|tyre" } }
rot = degrees to turn the model, length = override fit length, y = lift/lower, paint/wheel = custom name regexes.

## Licensing
Only use models you own or that allow commercial use (CC0 / CC-BY with credit / purchased license).
Remove real brand logos/badges (Apple may reject trademarked logos) - the game uses invented badges.

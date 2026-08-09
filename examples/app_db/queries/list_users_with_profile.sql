SELECT
  u.id AS user_id,
  u.email,
  p.bio AS profile_bio,
  p.avatar_url
FROM app.users AS u
LEFT JOIN app.user_profiles AS p ON p.user_id = u.id
ORDER BY u.id;
